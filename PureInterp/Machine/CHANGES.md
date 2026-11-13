# Changes to the loop's interface (SUB and RETURN)

For whoever glues `monad_pure_execute`'s entry and exit to `run_sim`.

## `Scratch`, `interp` (`Invariant.lean`)

- `Scratch` has a new last field `r7`. `interp` owns `(.x7 ↦ᵣ scr.r7)` (after
  `x6`). Why: `f_sub` uses `t2` (`x7`) as a temporary.

## `ExitEnv`, `exitFrame`, `final` (`Full.lean`)

- `ExitEnv` has a new field `fbase` (after `slot2`): the address of the ten
  doublewords directly below `slot2`. `Linked.fbase : E.fbase + 80 = E.slot2`,
  so `fbase = L.sp - 104`. These are the frame of `return_impl` (80 bytes;
  its `ra` slot is `slot2` itself) and the `ra` slot of the `Context::exit`
  it calls. They are machine-stack cells below the handler frame; the entry
  glue has to own them.
- `exitFrame E a1v g0 s2 st0 res fr` takes two more arguments and ends with
  `… ** words (E.ctx + 184) res ** words E.fbase fr`. `res` is the eight
  doublewords of `ctx.result.offset` (`ctx + 184`) and `ctx.result.size`
  (`ctx + 216`); the status field `ctx + 248` follows them as before.
  `run_sim` needs `res.length = 8` and `fr.length = 10`.
- `final L E scr limbs j12 j13 j14 js2 status g res fr`: new `j12` (`x12` is
  no longer `L.bottom` at the end: `memmove` uses `a2`), and the same two
  regions with their final contents. `final` also owns `(.x7 ↦ᵣ scr.r7)`.

## `Linked` (`Linked.lean`)

- Parameters are now `hS hA hB hP hU hR hI hRI hM`: `hB` is `f_sub`, `hR` is
  `f_return`, `hRI` is `f_return_impl`, `hM` is `f_memmove`.
- New fields: `cSub`, `cReturn`, `cReturnImpl`, `cMemmove`, `tSub` (0x03),
  `tReturn` (0xf3), `tblSub`, `eSubOog`, `eSubErr`, `eReturnErr`,
  `eReturnImpl`, `eMemmove`, `retAligned`, `eReturnExit`, `fbase`, and the
  layout facts RETURN's two `memmove(·, ·, 32)` calls need:
  `sal` and `ctxal` (operand stack and context doubleword-aligned), `below`
  (`L.bottom.toNat + 32 * 1025 ≤ E.ctx.toNat + 184`: the operand stack lies
  below the context's result fields, so `memmove` copies backwards),
  `ctxcover` (`E.ctx.toNat + 248 ≤ 2 ^ 64`), `svalid` and `rvalid` (byte
  access to the operand stack and to the 64 result bytes is valid).
- `OpOK` also accepts 0x03 and 0xf3.

## `ResultOK` (`Linked.lean`)

`ResultOK r mem status g res0 res` (was `ResultOK r status g`):

- failure: `r = ⟨.failure, 0, []⟩` and `status` is 2 or 3; or
- `status = 0`, `g = BitVec.ofNat 64 gas` with `gas < 2^63`, and either
  `res = res0 ∧ r = ⟨.success, gas, []⟩` (STOP: result words untouched), or
  `res = limbsOf off ++ limbsOf size ∧ r = Model.returnResult gas mem off size`
  (RETURN).

RETURN's handler charges nothing. `Model.returnResult` is the model of what
`Context::copy_result_data` then does with `gas_remaining`, `result.size`,
`result.offset` and the memory size `mem` (in words; `memory.size = 32 * mem`
and `memory.cost = cmem mem` are the facts to relate): size `≥ 2^28` fails;
size 0 succeeds with no output; offset `≥ 2^28` fails; otherwise charge
`cmem (max mem ⌈(off+size)/32⌉) - cmem mem` and return `size` zero bytes.
The exit glue has to prove the binary does that; for the STOP case it needs
what `copy_result_data` makes of the initial `res0`.

## `run_sim` (`Loop.lean`)

```
theorem run_sim (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) :
  ∀ fuel s r, Model.run code fuel s = some r → RunOK L hI code fuel s →
    ∀ scr limbs a1v g0 s2 st0 res fr,
      Rep limbs s.stack → s.gas < 2 ^ 63 → s.pc ≤ code.length + 1 →
      res.length = 8 → fr.length = 10 →
      ∃ scr' limbs' j12 j13 j14 js2 status g res' fr',
        ResultOK r s.mem status g res res' ∧
        cpsTripleWithin (464 * fuel) … cr
          (interp L scr limbs s.stack.length s.gas (30 + s.pc) ** exitFrame E a1v g0 s2 st0 res fr)
          (final L E scr' limbs' j12 j13 j14 js2 status g res' fr')
```

The step bound per instruction went from 44 to 464 (RETURN: 10 in `return_`,
430 in `return_impl` with two 197-step `memmove`s, 24 in the exit chain).

## Model and specification side

- `Model.State` has a new field `mem` (active memory in words; `Model.init`
  sets 0). `Model.cmem`, `Model.returnResult`; `Model.step` handles 0x03 and
  0xf3.
- `Spec.Matches'` has three more fields: `mem` (`e.activeWords.toNat =
  s.mem`), `memZero` (`e.memory.data = Array.replicate e.memory.size 0`) and
  `gasBound` (`s.gas + Model.cmem s.mem < Model.cmem (2 ^ 23)`).

## Bytecode buffer offset

`Linked.padded` is now `L.code = replicate 30 0 ++ code ++ replicate pad 0`
with `33 ≤ pad`: the buffer `Intercode::pad` builds, with `L.codeBase` its
(doubleword-aligned) start. Code byte `pc` is buffer byte `30 + pc`, so
`run_sim`'s precondition is `interp L scr limbs s.stack.length s.gas
(30 + s.pc)` (the instruction pointer is `L.codeBase + 30 + pc`).
`Linked.byte` and `Linked.next` take the buffer index `j` and the code index
`i` with `j = 30 + i`; `Linked.len` is `30 + code.length + 33 ≤
L.code.length`. The step and `*_final` theorems are unchanged.
