# monad-pure-interp

A Lean 4 effort to prove that the **RISC-V machine code** of the monad EVM
interpreter computes what a **Lean EVM specification** (EVMYulLean) says it
should, for contracts that touch no world state.

The proof is about the linked binary, not the C++ source: the compiler is not
trusted. The RISC-V semantics and program logic come from
[`Verified-zkEVM/riscv-zkvm`](https://github.com/Verified-zkEVM/riscv-zkvm)
v0.4.0; the EVM semantics from
[`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean),
ported here to Lean 4.33.1.

**Status.** For six opcodes (STOP, ADD, SUB, POP, PUSH1, RETURN) the
interpreter's handler loop in the real binary is proved to compute what
EVMYulLean's `EVM.X` computes. The entry and exit of the binary's entry point
are proved only in part, so the end-to-end theorem is stated but **not
proved**. Everything that is proved builds with no `sorry`, no added `axiom`
and no `native_decide` (about 8,650 lines of Lean, excluding the generated
image).

- `TODO.md`: what is missing and how to continue.
- `docs/DETAILS.md`: the proof recipe, library traps, and per-file notes.

## What is being verified

`./build.sh` compiles the unmodified monad interpreter sources
(`category/vm/interpreter`, `category/vm/runtime`) for one revision, Cancun,
into a closed freestanding RV64IM ELF, `build/pure.elf`: 181 functions,
11,117 instructions.

- **Pure subset.** Every opcode that touches world state, the block or
  transaction environment, logs or other contracts dispatches to the
  interpreter's own `invalid` handler. So do KECCAK256, TLOAD and TSTORE, for
  now. This is done by one table override in `cxx/pure_interp.cpp`; the
  handlers themselves are the monad sources.
- **Entry point.** `monad_pure_execute(input*, output*)`: bytecode, calldata
  and gas in a struct at a known address; status, remaining gas and output
  out.
- **Platform layer** (`cxx/platform.cpp`): a bump allocator and byte-loop
  `memcpy`/`memset`/`memmove`, chosen to be easy to verify.
- **Lean image** (`PureInterp/Image/`, generated): each function's raw words
  and decoded instructions, with a kernel-checked theorem that the words
  decode to the instructions.

## How the proof is structured

There are three layers, and an intermediate model between the binary and the
specification:

```
 RISC-V binary ──────────► Model.run ──────────► EVM.X  (EVMYulLean)
   machine-code proofs       Lean-only proof
   (separation logic)        (no RISC-V)
```

`PureInterp/Model.lean` is a 200-line executable definition of what a pure
contract can observe: operand stack, gas, pc, memory size. It exists because
`EVM.X` threads fuel, lives in `Except`, carries the whole world state and
checks conditions in an order the binary does not follow.

### How the results chain together

`✔` proved, `✘` missing, `◐` partly proved. Arrows read "is used by".

```
                    ┌──────────────────────────────────────────────┐
                    │  GOAL   Top.PureExecuteCorrect           ✘   │
                    │  monad_pure_execute(in, out) writes what     │
                    │  EVM.X returns, for any loaded machine state │
                    └──────────────────────▲───────────────────────┘
                                           │
        ┌──────────────────────────────────┼──────────────────────────────────┐
        │                                  │                                  │
┌───────┴────────────┐         ┌───────────┴────────────┐         ┌───────────┴───────────┐
│ ENTRY          ◐   │         │ LOOP               ✔   │         │ EXIT              ◐   │
│ call ──► first     │  ✘join  │ Top.loop_correct       │  ✘join  │ setjmp site ──►       │
│ handler, invariant ├────────►│ handler loop of the    ├────────►│ output struct, return │
│ established        │         │ real image = EVM.X     │         │                       │
└───────▲────────────┘         └───────────▲────────────┘         └───────────▲───────────┘
        │                                  │                                  │
 ✔ launch_region                ┌──────────┼──────────┐            ✔ trampoline_exit
   trampoline, setjmp,          │          │          │            ✔ fail_tail_error/_oog
   core_loop, 1st dispatch      │          │          │              (failure: status 2,
 ✔ pad_spec                     │          │          │               gas_left 0)
   buffer = 0³⁰ ++ code ++ 0³³  │          │          │            ✔ out_success
 ✔ malloc, memcpy, memset       │          │          │              (output struct writes)
 ◐ ctor_spec                    │          │          │            ✘ copy_to_result success
   (assumes find_jumpdests)     │          │          │              path, copy_result_data
 ✘ find_jumpdests               │          │          │              ◄── RETURN's gas and
 ✘ Context::from                │          │          │                  output live here
 ✘ first 44 instructions of     │          │          │            ✘ cleanup and final ret
   monad_pure_execute           │          │          │
                                │          │          │
              ┌─────────────────┘          │          └─────────────────┐
              │                            │                            │
  ┌───────────┴───────────┐    ┌───────────┴───────────┐    ┌───────────┴───────────┐
  │ Machine.run_sim   ✔   │    │ Top.linked_image  ✔   │    │ Spec.agrees       ✔   │
  │ binary loop computes  │    │ the real ELF has the  │    │ Model.run gives what  │
  │ Model.run, given the  │    │ layout run_sim        │    │ EVM.X gives           │
  │ image layout (Linked) │    │ assumes               │    │                       │
  └───────────▲───────────┘    └───────────▲───────────┘    └───────────▲───────────┘
              │                            │                            │
   per opcode, from the          f_x.included (181)           X_add, X_sub, X_pop,
   invariant:                    imageTable_0xNN (256)        X_push1, X_stop,
   ✔ add_step  sub_step          link_eq (call offsets)       X_return, decode_*
   ✔ pop_step  push1_step                                     u256_add, u256_sub
   ✔ stop_final return_final
   ✔ *_oog_final *_err_final
   ✔ invalid_final
              ▲
   raw handler theorems:
   ✔ add_spec sub_spec pop_spec
   ✔ push1_region return_spec
   ✔ exit_chain (Context::exit
     ──► longjmp)

 Trusted, not proved here:  ELF bytes = Lean image words  ·  ELF loader  ·
 riscv-zkvm's decoder and its link to Sail  ·  Lean kernel  ·  bv_decide (3 limb lemmas)
```

## The statements

Each snippet is copied from the source, with long hypothesis lists abridged
as `…`. `cpsTripleWithin n entry exit cr P Q` is the library's bounded triple:
from any state at `entry` satisfying `P` (plus any frame) whose code contains
`cr`, the machine reaches `exit` within `n` instructions in a state satisfying
`Q` (plus the same frame).

### The intermediate model — `PureInterp/Model.lean`

```lean
structure State where
  stack : List Word256   -- top first
  gas : Nat
  pc : Nat
  mem : Nat              -- active memory size in 32-byte words

def step (code : List Byte) (s : State) : Outcome :=
  match (byteAt code s.pc).toNat with
  | 0x00 => .halt ⟨.success, s.gas, []⟩                               -- STOP
  | 0x01 => charge s 3 fun s => binary s (· + ·)                      -- ADD
  | 0x03 => charge s 3 fun s => binary s (· - ·)                      -- SUB
  | 0x50 => …                                                         -- POP
  | 0x60 => …                                                         -- PUSH1
  | 0xf3 => …  returnResult s.gas s.mem off size                      -- RETURN
  | _ => failure
```

What a pure contract can observe, and one instruction of it. Every
exceptional halt is the single result `failure` with no gas and no output,
because that is all the binary reports. Reading past the end of the code is
STOP. `Model.run code fuel s` iterates `step` at most `fuel` times.

### Model agrees with EVMYulLean — `Spec.agrees` ✔

```lean
theorem agrees (code : List Model.Byte) (vj : Array UInt256) (fuel : ℕ) (s : Model.State)
    (r : Result) (e : EVM.State)
    (hm : Matches' code s e) (hsup : RunSupported code fuel s)
    (hrun : Model.run code fuel s = some r) :
    ResultMatches r (X (fuel + 1) vj e)
```

If the model halts with `r` within `fuel` instructions, then the Yellow Paper
loop `EVM.X`, started from any EVMYulLean state `e` describing the same point
of the same execution (`Matches'`), returns the matching result: the same
success or revert with the same gas and output, or some exception other than
running out of fuel. `RunSupported` restricts the run to opcodes the model
implements, plus the bytes EVMYulLean itself decodes as invalid. Pure Lean; no
RISC-V involved. `Matches'` carries a gas ceiling (about 1.37 × 10¹¹) under
which the binary's 2²⁸ bound on RETURN offsets is unobservable.

### One handler, raw — e.g. `Handlers.add_spec` ✔

```lean
theorem add_spec (base sp ra slot gas top bottom ip cw cwAddr entryAddr h : Word) …
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffd#12) 0)
    (hdepth : BitVec.slt ((0 : Word) + signExtend12 0x020#12) (top - bottom)) … :
    cpsTripleWithin 44 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_add.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** … ** (m0 ↦ₘ b0) ** … ** (n3 ↦ₘ a3) ** (tcell ↦ₘ h))
      (… ** (m0 ↦ₘ (b0 + a0)) ** (m1 ↦ₘ (a1 + b1 + cb (b0 + a0) b0)) ** …)
```

The ADD function as it sits in the binary, at the level of registers and
memory cells: with enough gas and two operands, 44 instructions later the
second stack slot holds the limb-wise sum with carries, the stack pointer has
dropped one slot, and the pc is the address stored in the instruction-table
cell for the next opcode byte.

### One handler, against the model — e.g. `Machine.sub_step` ✔

```lean
theorem sub_step (L : Layout) (scr : Scratch) (limbs : List Word) (base h : Word)
    (a b : Model.Word256) (rest : List Model.Word256) (gas pc : Nat)
    (hrep : Rep limbs (a :: b :: rest)) (hg3 : 3 ≤ gas) (hgb : gas < 2 ^ 63) … :
    ∃ scr' limbs', Rep limbs' ((a - b) :: rest) ∧
      cpsTripleWithin 44 base ((h + signExtend12 0x000#12) &&& ~~~1)
        (CodeReq.ofProg base Image.f_sub.prog)
        (interp L scr limbs (rest.length + 2) gas pc)
        (interp L scr' limbs' (rest.length + 1) (gas - 3) (pc + 1))
```

The same handler restated with the interpreter invariant. `interp` says "the
machine is at a handler entry": the pinned registers, the operand stack
array, the padded bytecode buffer and the instruction table. `Rep limbs stack`
says the stack array holds that model stack. So: from the invariant for a
model state with `a :: b :: rest` and at least 3 gas, the handler reaches the
next opcode's handler with the invariant for `(a - b) :: rest`, 3 less gas,
and pc + 1 — exactly what `Model.step` does.

### A halting path — e.g. `Machine.stop_final`, `add_oog_final` ✔

```lean
theorem stop_final (cr : CodeReq) (L : Layout) (E : ExitEnv) … :
    cpsTripleWithin 29 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E … ((0 : Word) + signExtend12 0x000#12) (BitVec.ofNat 64 gas) …)
```

From the invariant, through `Context::exit` and `longjmp`, to the address the
trampoline's `setjmp` saved. `exitFrame` is the runtime context and jump
buffer; `final` is the machine at that return site with a given status and gas
in the context. There is one such theorem for STOP, RETURN and the invalid
handler, and for each handler's out-of-gas and stack-error exits.

### The loop computes the model — `Machine.run_sim` ✔

```lean
theorem run_sim (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) :
    ∀ fuel s r, Model.run code fuel s = some r → RunOK L hI code fuel s →
    ∀ scr limbs a1v g0 s2 st0 (res fr : List Word),
      Rep limbs s.stack → s.gas < 2 ^ 63 → s.pc ≤ code.length + 1 → … →
      ∃ scr' limbs' j12 j13 j14 js2 status g res' fr', ResultOK r s.mem status g res res' ∧
        cpsTripleWithin (464 * fuel) (L.table.getD (Model.byteAt code s.pc).toNat 0)
          ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
          (interp L scr limbs s.stack.length s.gas (30 + s.pc) ** exitFrame E a1v g0 s2 st0 res fr)
          (final L E scr' limbs' j12 j13 j14 js2 status g res' fr')
```

By induction on the model's step count, composing the step and halting
theorems through the instruction table. If the model halts with `r`, the
machine goes from the invariant at the current opcode's handler to the
`setjmp` return site within `464 × fuel` instructions, and the context holds
`r` (`ResultOK`): its status, and on success its gas and, for RETURN, the
offset and size operands. `Linked` is the list of facts about the loaded
image this needs. The `30 +` is real: the binary puts the code 30 bytes into
its buffer.

### The real ELF has that layout — `Top.linked_image` ✔

```lean
theorem linked_image {L : Layout} {E : ExitEnv} {code : List Model.Byte} (D : Dyn L E code) :
    Linked Image.imageCode L E code Image.f_stop.addr Image.f_add.addr Image.f_sub.addr
      Image.f_pop.addr Image.f_push_1.addr Image.f_return.addr Image.f_invalid.addr
      Image.f_return_impl.addr Image.f_memmove.addr
```

Every static fact in `Linked` — where each function is, what each of the 256
instruction-table entries points to, every pc-relative call offset — is
proved from the extracted image. What remains in `Dyn` is the run-time layout
only: where the stack, context, jump buffer and bytecode buffer are, that
they are aligned and valid, and that the buffer is 30 zeros, the code, then
at least 33 zeros.

### Binary loop = EVMYulLean — `Top.loop_correct_machine` ✔

```lean
theorem loop_correct_machine (D : Dyn L E code)
    (hrun : Model.run code fuel s = some r) (hsup : Spec.RunSupported code fuel s)
    (hrep : Rep limbs s.stack) (hgas : s.gas < 2 ^ 63) (hpc : s.pc ≤ code.length + 1) …
    (m : MachineState) (hload : Image.ImageLoaded m)
    (hmpc : m.pc = Image.imageTable.getD (Model.byteAt code s.pc).toNat 0)
    (hpre : (interp L scr limbs s.stack.length s.gas (30 + s.pc) ** exitFrame E …).holdsFor m) :
    ∃ k, k ≤ 464 * fuel ∧ ∃ m', stepN k m = some m' ∧
      m'.pc = (E.v0 + signExtend12 0x000#12) &&& ~~~1 ∧
      ∃ … status g …, ResultOK r s.mem status g res res' ∧ (final …).holdsFor m' ∧
        m'.getMem (E.ctx + 248) = status ∧ m'.getMem (E.ctx + 8) = g ∧
        ∀ vj e, Spec.Matches' code s e → Model.ResultMatches r (EVM.X (fuel + 1) vj e)
```

**The strongest proved result.** Take any machine state with the real image
loaded, sitting at the handler of the current opcode with the invariant
holding. Then within `464 × fuel` steps of the RISC-V model the machine is at
the `setjmp` return site, the runtime context's status and gas cells hold the
result, and that result is the one `EVM.X` returns from any matching
EVMYulLean state. No separation logic in the conclusion's machine part: it is
a statement about `stepN`.

It is not yet about the entry point: it starts inside the interpreter and
ends inside it.

### Entry and exit pieces — `PureInterp/Entry/` ◐

- `launch_region` ✔ — `trampoline` → `setjmp` → `core_loop` → the first
  opcode's handler, 46 instructions.
- `pad_spec` ✔ — `Intercode::pad`: for any code size below 2²⁰ the buffer
  becomes `replicate 30 0 ++ code ++ replicate 33 0`, within `5n + 253`
  steps. Includes the `memcpy` and `memset` loops.
- `ctor_spec` ◐ — the `Intercode` constructor, assuming a contract for
  `find_jumpdests`.
- `fail_tail_error`, `fail_tail_oog` ✔ — from the return of `trampoline`
  through `copy_to_result` to the output struct: `status = 2, gas_left = 0`,
  no output.
- `out_success` ✔ — the output-struct writes for a successful result.

### The goal — `Top.PureExecuteCorrect` ✘ (a definition, not a theorem)

```lean
def PureExecuteCorrect : Prop :=
  ∀ (c : Call) (s : MachineState) (e : EvmYul.EVM.State) (fuel : Nat),
    AtCall c s →
    SpecStart c e →
    (Model.run c.code fuel (Model.init c.gas)).isSome →
    Spec.RunSupported c.code fuel (Model.init c.gas) →
    ∃ k, k ≤ stepBound c.code.length fuel ∧ ∃ s', stepN k s = some s' ∧
      s'.pc = c.ra &&& ~~~1 ∧
      s'.getReg .x2 = c.sp ∧
      Reports s' c.out
        (EvmYul.EVM.X (fuel + 1) (EvmYul.EVM.D_J (Model.toByteArray c.code) ⟨0⟩) e)
```

- `AtCall c s`: the image is loaded; the pc is at `monad_pure_execute`;
  `a0`, `a1`, `ra`, `sp` are set; memory holds the input struct, the
  bytecode, the operand-stack and EVM-memory buffers, the machine stack and
  the heap.
- `SpecStart c e`: `e` is EVMYulLean's start state for this code, calldata
  and gas.
- Conclusion: within a bounded number of steps the machine has returned to
  the caller with `sp` restored, and the output struct holds what `EVM.X`
  returned — status 0, 1 or 2, the remaining gas, and a pointer and size
  whose bytes are the output.

Parts of this statement are provisional and should be reviewed before anyone
proves it: `gas < 2³¹` (so RETURN cannot exhaust the 64 MiB heap), the heap
being all zero, the `stepBound` constants and the 4 KiB machine stack (only
`464 × fuel` is proved), and that "halts within `fuel` supported steps" is
phrased through the model.

## What is trusted

- **The Lean image equals the ELF.** The generator copies words out of the
  ELF; nothing re-checks them. The decode step (words → instructions) is
  kernel-checked.
- **The loader.** That the zkVM places those bytes at those addresses.
- **riscv-zkvm.** Its instruction semantics and its decoder; upstream has not
  yet tied the decoder to Sail's. The model executes a pre-decoded code map
  rather than fetching from memory.
- **EVMYulLean** as the specification, with one change in our fork:
  `ffi.ByteArray.zeroes` is a Lean `def` (`⟨Array.replicate n.toNat 0⟩`)
  instead of an opaque extern.
- **`bv_decide`** for three lemmas saying the limbs the handlers compute are
  the limbs of 256-bit addition, subtraction and a zero-extended byte.

Not trusted: GCC, the assembly rewriting pass (`tools/lower_w.py`), the image
generator's instruction lists, and the generators for linking facts.

## Layout

| Path | Contents |
|---|---|
| `cxx/`, `build.sh`, `tools/` | The binary's entry point and platform layer, the build, helper scripts. |
| `harness/` | Runs the ELF in the proof model (`run-pure`) and generates the Lean image (`gen-image`). |
| `PureInterp/Image/` | Generated image; `Link*.lean`: whole-image code requirement, instruction table, `ImageLoaded`. |
| `PureInterp/Model.lean` | The intermediate model. |
| `PureInterp/Spec/`, `Refine/` | Model against EVMYulLean; word and gas bridging lemmas. |
| `PureInterp/Handlers/` | Raw per-function machine-code theorems. |
| `PureInterp/Machine/` | Invariant, step and halting theorems, `Linked`, `run_sim`. |
| `PureInterp/Entry/` | Entry and exit glue for `monad_pure_execute`. |
| `PureInterp/Top/` | `linked_image`, `loop_correct`, `loop_correct_machine`, `PureExecuteCorrect`. |
| `spec/` | `evmyullean-lean-4.33.patch`: our changes to EVMYulLean. `tools/fetch_spec.sh` clones the pinned upstream commit into `spec/EVMYulLean/` and applies it. |
| `Test/` | Axiom audits. |

## Build and run

```bash
tools/fetch_spec.sh                                    # once: clone and patch EVMYulLean (then follow its hint)
./build.sh                                             # the ELF (do not rerun casually: see TODO.md)
(cd harness && nix shell nixpkgs#elan -c lake build)   # runner and image generator
nix shell nixpkgs#elan -c lake build                   # all proofs
nix shell nixpkgs#elan -c lake env lean Test/AxiomsTop.lean
harness/.lake/build/bin/run-pure build/pure.elf 600260030160005260206000f3 "" 100000
```

`build/pure.elf`, its symbol list and disassembly are committed: they are the
binary the proofs are about. They were built from the monad repository at
commit `93aa14035` (plus uncommitted zkVM state-layer changes that do not touch
the interpreter) with `riscv64-unknown-elf-gcc` 15.2.0. `build.sh` expects the
monad checkout at `$MONAD` (default `~/monad`) and the toolchain at
`$RISCV_TOOLCHAIN_DIR` (default `~/riscv_gcc`).

Rebuilding the ELF moves code, and the proofs contain literal offsets copied
from the disassembly, so they break until those are updated.
