# TODO

Notes for resuming. Read `README.md` for the picture and `docs/DETAILS.md` for
the proof recipe and library traps before touching proofs.

State on 2026-11-13: `nix shell nixpkgs#elan -c lake build` passes (1272
jobs); no `sorry`, no added `axiom`, no `native_decide`. Strongest result:
`Top.loop_correct_machine`. Goal: prove `Top.PureExecuteCorrect`
(`PureInterp/Top/Statement.lean`), currently a `def`.

## Before starting

- [ ] Do not run `./build.sh` unless you mean to. A rebuild moves code and
      breaks every proof that contains a literal offset. If you do: rerun
      `harness/.lake/build/bin/gen-image build/pure.elf build/symbols.txt PureInterp/Image`
      and `python3 tools/gen_link.py PureInterp/Image`, then fix literals.
- [ ] Fix the comment in `harness/PureAbi.lean`: the input struct is 64 bytes,
      not 56.

## A. Finish the end-to-end theorem for the six opcodes

In suggested order. Items 1 and 2 give the first true end-to-end statement
for failures and for STOP; item 3 is where RETURN becomes real.

1. [ ] **Join launch to the loop.** From `Entry.launch_region`'s
       postcondition establish
       `interp L scr limbs 0 gas 30 ** exitFrame E …` with a `Top.Dyn L E code`.
       Mapping (from the entry agent's report): `L.sp = sp_tramp − 256`,
       `L.ra = bt + 72`, `L.bottom = stk`; `E.ctx = ctx`, `E.jb = spf + 32`,
       `E.v0 = bt + 32`, `E.v1..v12 = E.c0..c11`, `E.v13 = spf`. Needs: fold
       the 14 jump-buffer cells and the table cell into `exitFrame` and
       `words L.tbl`; carry the trampoline frame slots as a frame; own the
       ten doublewords at `E.fbase`; convert `ImageLoaded`'s pointwise data
       fact into `words Image.tableAddr Image.imageTable`.
2. [ ] **Join the loop to the exit tails.** `final` (with `x10 = 1`,
       `x2 = E.v13`) feeds `trampoline_exit` and `fail_tail_error` /
       `fail_tail_oog`. Instantiate the `Entry` theorems with
       `Image.imageCode` using `f_x.included` and `link_eq`.
3. [ ] **Success exit: `copy_to_result` (idx 6–62) and `copy_result_data`
       (158 instructions).** This computes RETURN's memory-expansion gas and
       output buffer; prove it yields `Model.returnResult`. Needs the context's
       memory fields (`memory.size = 32 * mem`, `memory.cost = cmem mem`) in
       `exitFrame`. `malloc`, `memcpy`, `out_success` are ready. Check in the
       disassembly whether GCC folded `malloc + memset` into `calloc` (the
       platform `calloc` does not clear, hence the zero-heap precondition).
4. [ ] **`Context::from`** (84 instructions) and
       `PureHost::get_tx_context`; **first 44 instructions of
       `monad_pure_execute`**. Both `memset` stack memory that is later read
       as doublewords: first write the `bytesRegion` ↔ `↦ₘ`/`words`
       conversion lemma.
5. [ ] **Cleanup and return**: `monad_pure_execute` idx 60–99 (`free` ×2,
       `~Intercode`, exception-pointer release, frame pop, `ret`).
6. [ ] **`find_jumpdests`** (121 instructions): discharge `ctor_spec`'s `hfj`.
       Nothing in the current subset reads the bitmap, so termination and
       "writes only its own allocation" suffice until JUMP/JUMPI.
7. [ ] **Prove `PureExecuteCorrect`**, first revisiting its provisional parts:
       `gas < 2^31` and that the heap suffices under it; the zero-heap
       requirement; `stepBound` and `machineStackBytes` (measure, then prove);
       pointer alignment.

## B. Remove restrictions

- [ ] Forward `memmove` (removes `Dyn.below` / `AtCall.stackBelow`).
- [ ] Converse of `Spec.agrees`, so the top-level statement need not mention
      `Model.run` and `RunSupported`.
- [ ] A static, code-only sufficient condition for `RunSupported`.
- [ ] Fold the extra conditions of `Spec.Matches'` (stack ≤ 1024, code length,
      memory facts, gas ceiling) into `Model.Matches`, and delete the false
      `Model.AgreesWithSpec`.

## C. More opcodes

Each opcode needs: raw handler theorem, step (or final) theorem against the
invariant, failure exits, a `Model.step` case, an `X_*` lemma and decoder
lemma, and fields in `Linked`/cases in `run_sim` and `step_sim`.

- [ ] **Write the generator first.** The handler proofs, the failure exits
      and the `Linked` fields are regular and carry literal offsets;
      `Machine/Fail.lean` was already produced from a Python template. A
      generator from the disassembly makes rebuilds survivable. (Hand proofs were wanted first;
      seven exist now.)
- [ ] Simple, same shape as ADD/POP/PUSH1: AND, OR, XOR, NOT, ISZERO, LT, GT,
      SLT, SGT, EQ, BYTE, SHL, SHR, SAR, SIGNEXTEND, DUP1–16, SWAP1–16,
      PUSH0, PUSH2–32, PC, GAS, JUMPDEST, CALLVALUE, CALLDATASIZE, CODESIZE.
      Raw proofs for JUMPDEST and SWAP1 exist (`Handlers/`).
- [ ] Jumps: JUMP, JUMPI. Needs `find_jumpdests` proved for real and its
      bitmap related to the spec's valid-jump set (`D_J` is `partial`; target
      `X`'s `validJumps` parameter).
- [ ] Memory: MLOAD, MSTORE, MSTORE8, MSIZE, MCOPY, CALLDATALOAD,
      CALLDATACOPY, CODECOPY, RETURNDATASIZE/COPY; REVERT. Needs memory
      contents in the model and invariant, and the reallocation path
      (`monad_vm_runtime_increase_capacity`).
- [ ] Hard arithmetic, last: MUL, DIV, SDIV, MOD, SMOD, ADDMOD, MULMOD, EXP
      (`udivrem`, `knuth_div`, shift-subtract 128-bit division).
- [ ] Re-enable KECCAK256 (spec has no Lean keccak: uninterpreted on both
      sides, or prove a software keccak against a Lean one) and TLOAD/TSTORE
      (spec needs an account at `codeOwner`).

## D. Trust and hygiene

- [ ] Build-time check that the words in `PureInterp/Image/` equal the ELF's
      `.text` and `.rodata`, or state the final theorem over the raw bytes.
- [ ] A formal ELF-loading statement; track upstream riscv-zkvm for the
      decoder-to-Sail link and the fetch-from-memory gap.
- [ ] Report upstream: `runBlock` leaves an unassigned metavariable when the
      `pcFree` side goal of a frame fails (symptom: "don't know how to
      synthesize placeholder" on every line).
- [ ] Drop `tools/lower_w.py` once riscv-zkvm models the RV64 word
      instructions (ADDW, SUBW, MULW, SLLIW, SRLIW, SRAIW); today the verified
      binary is the lowered one, not what a plain `-march=rv64im` build emits.
      The production ZisK guest additionally uses Zba/Zbb/Zbs/Zbkb, which the
      library does not model either.
- [ ] Decide whether to keep `bv_decide` for the limb lemmas or prove them by
      hand to drop its axioms.
- [ ] `docs/DETAILS.md` is the old README; its early sections predate the
      later work and should be reconciled with the code.

## Open questions

- Is `gas < 2^31` an acceptable top-level bound, or should the heap be sized
  from the gas instead?
- Environment opcodes (ORIGIN, TIMESTAMP, CHAINID, …) are invalid now; should
  they become fixed inputs?
- Keep software byte-loop `memmove` (RETURN costs ~430 steps) or switch to
  something faster and harder to prove?
