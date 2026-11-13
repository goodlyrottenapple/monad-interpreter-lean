import PureInterp.Top.Loop

/-!
# The intended end-to-end statement

`PureExecuteCorrect` is the claim this project works towards: calling
`monad_pure_execute` in the RISC-V model returns what EVMYulLean's `EVM.X`
returns. **It is a definition of a proposition, not a theorem.** It is
type-checked against the real definitions (the image, the machine model,
EVMYulLean); nothing in this file proves it.

Three constants in it are estimates that no proof has yet confirmed:
`machineStackBytes` (4096; the frames on the deepest supported path add up to
about 1.1 kB), the step bound `stepBound` (`464 * fuel` is proved by
`run_sim`; the `32 * codeLen + 8192` for entry and exit is taken from runs of
the harness, which show about 2,500 steps of fixed cost and about 20 per code
byte), and the gas bound `2^31` (see `PureExecuteCorrect`). If a proof finds
one too small, the statement has to change.

## What is proved towards it

* **The loop, against the real image and EVMYulLean** — `Top.loop_correct`
  (and `Top.loop_correct_machine` on machine states): from
  `Machine.interp … ** Machine.exitFrame …` at the handler of the current
  opcode to `Machine.final …` at the `setjmp` return site with
  `Machine.ResultOK`, over `Image.imageCode`, together with
  `Model.ResultMatches r (EVM.X …)`. It rests on `Machine.run_sim`,
  `Top.linked_image` (every static field of `Machine.Linked` discharged) and
  `Spec.agrees`. Its hypotheses about the run-time layout are `Top.Dyn`.
* **Entry, in pieces** (`PureInterp/Entry/`, each over an arbitrary code
  requirement with inclusion and call-target hypotheses, not yet instantiated
  with the image):
  * `pad_spec`: `Intercode::pad` builds `replicate 30 0 ++ code ++
    replicate 33 0` in a fresh 32-aligned heap block (over `alloc32_spec` /
    `new_9fb4_spec`, `memset_spec`, `memcpy_spec`);
  * `ctor_spec`: the `Intercode` constructor, **conditional on `hfj`**, a
    hypothesis that is the whole contract of `find_jumpdests`;
  * `launch_region` (over `trampoline_enter`, `setjmp_spec`,
    `trampoline_call`, `core_loop_spec`): from the call of `trampoline` to the
    entry of the first opcode's handler, with the machine in the shape of
    `interp … 0 gas … ** exitFrame …`, stated in raw cells.
* **Exit, in pieces**:
  * `trampoline_exit` (`trampoline_leave`): from the `setjmp` return site with
    `a0 ≠ 0` back to `trampoline`'s caller;
  * `fail_tail_error`, `fail_tail_oog` (over `copy_to_result_error`,
    `copy_to_result_oog`, `out_nonzero`): from the return of `trampoline`
    with context status 2 or 3 to the last store into the output struct
    (`status = 2`, the other three fields 0);
  * `out_success`: the 13 instructions that write the output struct from a
    `vm::Result` with status code 0.

## What is missing

1. `find_jumpdests` (121 instructions): `ctor_spec`'s hypothesis `hfj`.
2. `Context::from` (and `PureHost::get_tx_context`, which it calls).
3. The first 44 instructions of `monad_pure_execute` (frame, `memset` of the
   message, reading the input struct, the three calls) as one triple that
   uses `ctor_spec` and `launch_region`, and its last 40 instructions (the
   cleanup after the output struct is written: `free`, `~Intercode`, frame
   pop, return).
4. `copy_to_result`'s success path and `Context::copy_result_data`. That
   function is where RETURN's memory-expansion gas is charged and where the
   output buffer is produced (`calloc`, relying on never-used heap being
   zero). Until it is proved, `Model.returnResult` is tied to machine code
   only through `Machine.ResultOK`, which says the context holds the offset
   and size words that `returnResult` is a function of; that the binary
   computes that function is not shown. STOP's success path goes through the
   same code with the initial result words.
5. The layer between the pieces and the loop: showing that `launch_region`'s
   postcondition is `interp L … 0 gas 30 ** exitFrame E …` for a layout
   satisfying `Top.Dyn` (the buffer from `pad_spec`, `L.sp = sp - 704 - 256`,
   `E.ctx = sp - 704 + 352`, `E.jb`, the frame cells `E.slot2`, `E.fbase`),
   and unpacking `final` for `trampoline_exit` and the tails.
6. Instantiating the Entry theorems with `Image.imageCode` (their inclusion
   and call-target hypotheses, by `f_x.included` and `link_eq` as in
   `Top.linked_image`).
7. Forward `memmove`: `run_sim` covers only the case where the operand stack
   lies below the context (`Dyn.below`), which is why `PureExecuteCorrect`
   assumes `stackBelow`.
8. A proof that a run of `EVM.X` that does not run out of fuel makes the
   model halt (the converse of `Spec.agrees`); without it the statement's
   run restriction has to mention the model.
9. All other opcodes; and, inherited from riscv-zkvm, the link from its
   decoder and step function to the Sail model.
-/

namespace PureInterp.Top
open RiscvZkvm.Rv64 PureInterp.Machine
open EvmYul (UInt256)
open EvmYul.EVM (ExecutionException ExecutionResult)

set_option maxRecDepth 100000

/-! ## The heap symbols (`cxx/link.ld`, `build/pure.map`) -/

/-- Address of the bump allocator's pointer, `heap_next` (`cxx/platform.cpp`). -/
def heapNextCell : Word := 0xa0000960

/-- `monad_pure_heap`: the first heap byte, and the initial `heap_next`. -/
def heapBase : Word := 0xa0000980

/-- The heap is 64 MiB (`monad_pure_heap_end = 0xa4000980`). -/
def heapBytes : Nat := 0x4000000

/-- `heap_next` is the last doubleword of the image's data segment, and the
    image initialises it to `monad_pure_heap`. So `Image.ImageLoaded s`
    already fixes the allocator's starting point. -/
theorem heapNextCell_initial :
    heapNextCell = Image.data0.addr + BitVec.ofNat 64 (8 * 300) ∧
    Image.dataWord 300 = heapBase := by
  constructor <;> decide

/-! ## One call -/

/-- The arguments of one call of `monad_pure_execute(in, out)`. -/
structure Call where
  /-- `a0`: address of the `monad_pure_input` struct (8 doublewords). -/
  inp : Word
  /-- `a1`: address of the `monad_pure_output` struct (4 doublewords). -/
  out : Word
  /-- `ra` and `sp` at the call. -/
  ra : Word
  sp : Word
  /-- The contract's bytecode and where it is in memory (`in->code`). -/
  code : List Model.Byte
  codePtr : Word
  /-- The call data and where it is in memory (`in->calldata`). -/
  calldata : List Model.Byte
  calldataPtr : Word
  /-- `in->gas`. -/
  gas : Nat
  /-- `in->memory`: the scratch buffer for EVM memory. -/
  memPtr : Word
  /-- The doubleword at `in + 48`: `memory_capacity` in its low 32 bits, then
      4 bytes of struct padding (not read). -/
  capWord : Word
  /-- `in->stack`: the operand stack buffer, 1025 slots of 32 bytes. -/
  stackPtr : Word

/-- `in->memory_capacity`, in bytes. -/
def Call.memCap (c : Call) : Nat := c.capWord.toNat % 2 ^ 32

/-- Bytes of machine stack below `sp` the call may use. -/
def machineStackBytes : Nat := 4096

/-- The memory the call needs, as one separation-logic assertion; the
    separating conjunction makes the nine regions pairwise disjoint. Each
    doubleword cell also asserts that its address is a valid, 8-aligned RAM
    address, so the pointers involved are necessarily doubleword-aligned.

    * the input struct, holding the eight fields in declaration order;
    * the output struct, with any contents `outw` (4 doublewords);
    * the bytecode and the call data, as bytes;
    * the EVM memory buffer: `memCap` bytes, **all zero**;
    * the operand stack buffer, with any contents `opstack` (4 · 1025
      doublewords);
    * the machine stack: `machineStackBytes` bytes below `sp`, any contents;
    * the allocator pointer `heap_next`, at its initial value, and the heap:
      64 MiB, **all zero** (`calloc` in `cxx/platform.cpp` does not clear;
      RETURN's output buffer comes from it). -/
def Call.memory (c : Call) (outw opstack mstack : List Word) : Assertion :=
  words c.inp [c.codePtr, BitVec.ofNat 64 c.code.length,
               c.calldataPtr, BitVec.ofNat 64 c.calldata.length,
               BitVec.ofNat 64 c.gas, c.memPtr, c.capWord, c.stackPtr] **
  words c.out outw **
  bytesRegion c.codePtr c.code **
  bytesRegion c.calldataPtr c.calldata **
  bytesRegion c.memPtr (List.replicate c.memCap 0) **
  words c.stackPtr opstack **
  words (c.sp - BitVec.ofNat 64 machineStackBytes) mstack **
  (heapNextCell ↦ₘ heapBase) **
  words heapBase (List.replicate (heapBytes / 8) 0)

/-- The machine state `s` is at a call of `monad_pure_execute` described by `c`. -/
structure AtCall (c : Call) (s : MachineState) : Prop where
  /-- The text segment is in the code map and the data segment (with the
      instruction table and the initial `heap_next`) is in memory. -/
  loaded : Image.ImageLoaded s
  /-- The pc is at the function's entry. -/
  pc : s.pc = Image.f_monad_pure_execute.addr
  /-- The two arguments, the return address and the stack pointer. -/
  a0 : s.getReg .x10 = c.inp
  a1 : s.getReg .x11 = c.out
  ra : s.getReg .x1 = c.ra
  sp : s.getReg .x2 = c.sp
  /-- The memory regions of `Call.memory`, for some initial contents of the
      output struct, the operand stack buffer and the machine stack. -/
  memory : ∃ outw opstack mstack : List Word,
    outw.length = 4 ∧ opstack.length = 4 * 1025 ∧ mstack.length = machineStackBytes / 8 ∧
    (c.memory outw opstack mstack).holdsFor s
  /-- The operand stack buffer lies below the machine stack. (The regions
      are disjoint, so the alternative is that it lies above. Only this
      order is covered: see item 7 of the module comment.) -/
  stackBelow : c.stackPtr.toNat < c.sp.toNat
  /-- `Intercode::pad` rejects code of `2^20` bytes or more. -/
  codeSize : c.code.length < 2 ^ 20
  /-- The context keeps the call data size in 32 bits. -/
  calldataSize : c.calldata.length < 2 ^ 32
  /-- Gas is below `2^31`. This gives three things at once: the binary's
      signed 64-bit gas counter is non-negative (`< 2^63`); the gas cannot
      pay for `2^23` words of memory, which `Spec.agrees` needs
      (`Spec.Matches'.gasBound`); and it cannot pay for `2^20` words (32 MiB)
      of memory (`2^31 ≤ Model.cmem (2^20)`), so RETURN's output, the padded
      code and the jump-destination bitmap fit in the 64 MiB heap and the
      allocator does not abort. -/
  gas : c.gas < 2 ^ 31

/-- The EVMYulLean state `e` is the start of the same call: this code and
    call data, `gas` gas, pc 0, empty stack, no active memory, and memory
    holding only zeros. Every other field (accounts, block, sender, …) is
    unconstrained: the opcodes covered do not read them. -/
structure SpecStart (c : Call) (e : EvmYul.EVM.State) : Prop where
  code : e.executionEnv.code = Model.toByteArray c.code
  calldata : e.executionEnv.calldata = Model.toByteArray c.calldata
  gas : e.gasAvailable.toNat = c.gas
  pc : e.pc.toNat = 0
  stack : e.stack = []
  activeWords : e.activeWords.toNat = 0
  memZero : e.memory.data = Array.replicate e.memory.size 0

/-- The output struct at `out` in machine state `s'` holds `status`, `gasLeft`,
    and a pointer and size whose bytes in `s'` are `output`. -/
def OutputIs (s' : MachineState) (out status : Word) (gasLeft : Nat) (output : ByteArray) : Prop :=
  s'.getMem out = status ∧
  s'.getMem (out + 8) = BitVec.ofNat 64 gasLeft ∧
  s'.getMem (out + 24) = BitVec.ofNat 64 output.size ∧
  (s'.readBytes (s'.getMem (out + 16)) output.size).map (fun b => UInt8.ofNat b.toNat) =
    output.data.toList

/-- The output struct reports the result of `EVM.X`: status 0 with the gas
    left and the output on success; status 1 likewise on revert; status 2
    with no gas and no output on any exceptional halt. (Running out of
    *fuel* is not an EVM outcome; the hypotheses of `PureExecuteCorrect`
    exclude it.) -/
def Reports (s' : MachineState) (out : Word) :
    Except ExecutionException (ExecutionResult EvmYul.EVM.State) → Prop
  | .ok (.success e o) => OutputIs s' out 0 e.gasAvailable.toNat o
  | .ok (.revert g o) => OutputIs s' out 1 g.toNat o
  | .error err => err ≠ .OutOfFuel ∧ OutputIs s' out 2 0 .empty

/-- Machine steps allowed for a run of `fuel` EVM instructions on `codeLen`
    bytes of code. -/
def stepBound (codeLen fuel : Nat) : Nat := 464 * fuel + 32 * codeLen + 8192

/-- **The intended top-level statement (not proved).**

    Take any call `c`, any machine state `s` at that call (`AtCall`), any
    EVMYulLean state `e` at the start of the same call (`SpecStart`), and any
    `fuel` such that the run takes at most `fuel` EVM instructions
    (`hhalt`), all of them supported (`hsup`: STOP, ADD, SUB, POP, PUSH1,
    RETURN, or a byte EVMYulLean decodes to `INVALID`).

    Then within `stepBound c.code.length fuel` steps of the RV64 model the
    machine is at the return address (`ra` with bit 0 cleared) with the
    stack pointer restored, and the output struct reports what
    `EVM.X (fuel + 1)` returns from `e`, with the code's valid jump
    destinations `D_J`.

    `hhalt` and `hsup` speak of the intermediate model (`Model.run`,
    `Spec.RunSupported`) because "at most `fuel` instructions, all supported"
    is so far only defined there; by `Spec.agrees` they imply that `EVM.X`
    does not run out of fuel. -/
def PureExecuteCorrect : Prop :=
  ∀ (c : Call) (s : MachineState) (e : EvmYul.EVM.State) (fuel : Nat),
    AtCall c s →
    SpecStart c e →
    (hhalt : (Model.run c.code fuel (Model.init c.gas)).isSome) →
    (hsup : Spec.RunSupported c.code fuel (Model.init c.gas)) →
    ∃ k, k ≤ stepBound c.code.length fuel ∧ ∃ s', stepN k s = some s' ∧
      s'.pc = c.ra &&& ~~~1 ∧
      s'.getReg .x2 = c.sp ∧
      Reports s' c.out
        (EvmYul.EVM.X (fuel + 1) (EvmYul.EVM.D_J (Model.toByteArray c.code) ⟨0⟩) e)

/-! ## Consistency with what is proved

Small checks that the statement's hypotheses are the ones the proved
theorems consume. -/

/-- The gas bound gives the three facts its comment claims. -/
theorem gas_bound_facts (gas : Nat) (h : gas < 2 ^ 31) :
    gas < 2 ^ 63 ∧ gas + Model.cmem 0 < Model.cmem (2 ^ 23) ∧ gas < Model.cmem (2 ^ 20) := by
  have h0 : Model.cmem 0 = 0 := by decide
  have h1 : Model.cmem (2 ^ 23) = 137464119296 := by decide
  have h2 : Model.cmem (2 ^ 20) = 2150629376 := by decide
  rw [h0, h1, h2]
  omega

/-- The statement's start states are the ones `Spec.agrees` (and so
    `loop_correct`) applies to. -/
theorem SpecStart.matches {c : Call} {e : EvmYul.EVM.State} (h : SpecStart c e)
    (hcode : c.code.length < 2 ^ 20) (hgas : c.gas < 2 ^ 31) :
    Spec.Matches' c.code (Model.init c.gas) e where
  code := h.code
  stack := by rw [h.stack]; rfl
  gas := h.gas
  pc := h.pc
  stackLen := by simp [Model.init]
  codeLen := by
    have : (2 : Nat) ^ 20 + 1 < 2 ^ 256 := by decide
    omega
  mem := h.activeWords
  memZero := h.memZero
  gasBound := (gas_bound_facts c.gas hgas).2.1

/-- Under the statement's hypotheses `EVM.X` returns the model's result; in
    particular it does not run out of fuel. -/
theorem spec_result {c : Call} {e : EvmYul.EVM.State} {fuel : Nat} (h : SpecStart c e)
    (hcode : c.code.length < 2 ^ 20) (hgas : c.gas < 2 ^ 31)
    (hhalt : (Model.run c.code fuel (Model.init c.gas)).isSome)
    (hsup : Spec.RunSupported c.code fuel (Model.init c.gas)) :
    ∃ r, Model.run c.code fuel (Model.init c.gas) = some r ∧
      Model.ResultMatches r
        (EvmYul.EVM.X (fuel + 1) (EvmYul.EVM.D_J (Model.toByteArray c.code) ⟨0⟩) e) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hhalt
  exact ⟨r, hr, Spec.agrees c.code _ fuel _ r e (h.matches hcode hgas) hsup hr⟩

end PureInterp.Top
