import EvmYul.EVM.Semantics
import PureInterp.Refine.Word

/-!
# Intermediate model of the pure interpreter

A small executable definition of what the binary computes, sitting between
the machine code and EVMYulLean:

    RISC-V binary  ──(handler proofs, simulation loop)──▶  Model.run
    Model.run      ──(Lean-only proof, no RISC-V)──────▶  EVM.X  (EVMYulLean)

It exists because `EVM.X` is awkward to target directly from machine-code
proofs: it threads fuel, lives in `Except`, carries the whole world state, and
checks conditions in an order the binary does not follow. The model has only
what a pure contract can observe.

Deliberate differences from EVMYulLean, each to be justified by the second
arrow rather than assumed:

* Every exceptional halt (out of gas, stack underflow or overflow, invalid or
  disabled opcode, bad jump) is the single result `failure` with no gas left
  and no output. That is all the binary reports.
* Gas is a natural number. The binary keeps it in a signed 64-bit register, so
  the first arrow needs the initial gas to be below `2^63`.
* Reading an opcode past the end of the code gives `STOP`, as both the padded
  bytecode buffer in the binary and `decode … |>.getD STOP` in `X` do.

STOP, ADD, SUB, POP, PUSH1 and RETURN are filled in so far; every other opcode
currently fails. Nothing writes memory yet, so the state carries only its
active size, which RETURN's expansion charge needs.
-/

namespace PureInterp.Model

abbrev Word256 := BitVec 256
abbrev Byte := BitVec 8

/-- What a running pure contract can observe and change. -/
structure State where
  /-- Operand stack, top first. -/
  stack : List Word256
  /-- Gas remaining. -/
  gas : Nat
  /-- Index of the next opcode in the code. -/
  pc : Nat
  /-- Active memory size in 32-byte words. No opcode of the model writes
      memory yet, so its contents are all zero and only the size matters. -/
  mem : Nat
  deriving Repr

inductive Status where
  | success | revert | failure
  deriving Repr, DecidableEq

/-- What `monad_pure_execute` writes to its output struct. -/
structure Result where
  status : Status
  gasLeft : Nat
  output : List Byte
  deriving Repr

inductive Outcome where
  | next (s : State)
  | halt (r : Result)

/-- Any exceptional halt. -/
def failure : Outcome := .halt ⟨.failure, 0, []⟩

/-- The code byte at `i`; zero (STOP) past the end. -/
def byteAt (code : List Byte) (i : Nat) : Byte := code.getD i 0

/-- Charge `cost` gas, failing if there is not enough. -/
def charge (s : State) (cost : Nat) (k : State → Outcome) : Outcome :=
  if s.gas < cost then failure else k { s with gas := s.gas - cost }

/-- An opcode that replaces the top two words by one and advances by one byte. -/
def binary (s : State) (f : Word256 → Word256 → Word256) : Outcome :=
  match s.stack with
  | a :: b :: rest => .next { s with stack := f a b :: rest, pc := s.pc + 1 }
  | _ => failure

/-- Push one word; the stack holds at most 1024. -/
def push (s : State) (w : Word256) (width : Nat) : Outcome :=
  if s.stack.length ≥ 1024 then failure
  else .next { s with stack := w :: s.stack, pc := s.pc + width }

/-- The Yellow Paper's memory cost for `a` active words. -/
def cmem (a : Nat) : Nat := 3 * a + a * a / 512

/-- The result of RETURN with `gas` left, `mem` active memory words, and the
    operands `off` and `size`, as `Context::copy_result_data` computes it:
    a size or (for non-empty output) an offset of `2^28` or more is out of
    gas; otherwise the expansion of memory to cover `off + size` is charged
    and the output is that many bytes of (zero) memory. -/
def returnResult (gas mem : Nat) (off size : Word256) : Result :=
  if 2 ^ 28 ≤ size.toNat then ⟨.failure, 0, []⟩
  else if size.toNat = 0 then ⟨.success, gas, []⟩
  else if 2 ^ 28 ≤ off.toNat then ⟨.failure, 0, []⟩
  else
    let cost := cmem (max mem ((off.toNat + size.toNat + 31) / 32)) - cmem mem
    if gas < cost then ⟨.failure, 0, []⟩
    else ⟨.success, gas - cost, List.replicate size.toNat 0⟩

/-- Execute the instruction at `s.pc`. -/
def step (code : List Byte) (s : State) : Outcome :=
  match (byteAt code s.pc).toNat with
  | 0x00 => .halt ⟨.success, s.gas, []⟩                               -- STOP
  | 0x01 => charge s 3 fun s => binary s (· + ·)                      -- ADD
  | 0x03 => charge s 3 fun s => binary s (· - ·)                      -- SUB
  | 0x50 => charge s 2 fun s =>                                       -- POP
      match s.stack with
      | _ :: rest => .next { s with stack := rest, pc := s.pc + 1 }
      | [] => failure
  | 0x60 => charge s 3 fun s =>                                       -- PUSH1
      push s ((byteAt code (s.pc + 1)).zeroExtend 256) 2
  | 0xf3 =>                                                           -- RETURN
      match s.stack with
      | off :: size :: _ => .halt (returnResult s.gas s.mem off size)
      | _ => failure
  | _ => failure

/-- Run for at most `fuel` instructions; `none` if still running. -/
def run (code : List Byte) : Nat → State → Option Result
  | 0, _ => none
  | fuel + 1, s =>
    match step code s with
    | .halt r => some r
    | .next s' => run code fuel s'

/-- Entry state for a call with `gas` gas. -/
def init (gas : Nat) : State := { stack := [], gas := gas, pc := 0, mem := 0 }

/-! ## The second arrow, stated

These are the statements to be proved against EVMYulLean; they are
definitions of propositions, not theorems, until proved. -/

open EvmYul in
/-- The code as EVMYulLean holds it. -/
def toByteArray (code : List Byte) : ByteArray := ⟨(code.map fun b => UInt8.ofNat b.toNat).toArray⟩

open EvmYul in
/-- A model state and an EVMYulLean state describe the same point of the same
    execution. Fields the model lacks are unconstrained. -/
structure Matches (code : List Byte) (s : State) (e : EVM.State) : Prop where
  code : e.executionEnv.code = toByteArray code
  stack : e.stack = s.stack.map Refine.u256
  gas : e.gasAvailable.toNat = s.gas
  pc : e.pc.toNat = s.pc

open EvmYul in
/-- A model result and what `EVM.X` returned agree. -/
def ResultMatches (r : Result) :
    Except EVM.ExecutionException (EVM.ExecutionResult EVM.State) → Prop
  | .ok (.success e o) => r.status = .success ∧ e.gasAvailable.toNat = r.gasLeft ∧
      o = toByteArray r.output
  | .ok (.revert g o) => r.status = .revert ∧ g.toNat = r.gasLeft ∧ o = toByteArray r.output
  | .error e => r.status = .failure ∧ e ≠ .OutOfFuel

open EvmYul in
/-- **Model agrees with EVMYulLean.** Whenever the model halts within `fuel`
    instructions, the Yellow Paper loop started from any matching state halts
    with the matching result. `jumps` is the set of valid jump destinations of
    the code; it becomes relevant once JUMP and JUMPI are in the model. -/
def AgreesWithSpec : Prop :=
  ∀ (code : List Byte) (fuel : Nat) (s : State) (r : Result) (e : EVM.State),
    Matches code s e → run code fuel s = some r →
    ResultMatches r (EVM.X (fuel + 1) (EVM.D_J (toByteArray code) ⟨0⟩) e)

end PureInterp.Model
