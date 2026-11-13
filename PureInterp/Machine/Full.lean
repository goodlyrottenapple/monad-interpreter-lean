import PureInterp.Machine.Exit
import PureInterp.Machine.AddStep
import PureInterp.Machine.SubStep
import PureInterp.Machine.PopStep
import PureInterp.Machine.Push1Step

/-!
# The whole interpreter state, and STOP

`interp` covers what handlers use while the loop runs. Halting also touches
the runtime context and the jump buffer; `exitFrame` holds those, untouched
by ordinary handlers. `final` is the machine at the `setjmp` return site.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

/-- What the exit path needs, fixed for one execution. -/
structure ExitEnv where
  /-- Address of the runtime context. -/
  ctx : Word
  /-- Address of the jump buffer the trampoline filled. -/
  jb : Word
  /-- Entry addresses of `Context::exit` and `longjmp`. -/
  be : Word
  bl : Word
  /-- Address of the frame slot `Context::exit` spills `ra` to. -/
  slot2 : Word
  /-- Address of the ten doublewords below `slot2` (`fbase + 80 = slot2`):
      the frames of `return_impl` and of the `Context::exit` it calls. -/
  fbase : Word
  /-- Callee-saved registers `s0`–`s11` while the loop runs. -/
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Word)
  /-- Jump buffer contents: `ra`, `s0`–`s11`, `sp`. -/
  (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Word)

/-- Context fields, jump buffer and callee-saved registers. `a1v` is the
    intercode pointer in `a1`; `g0`, `st0` are the context's gas and status
    fields, `s2` the content of the exit frame slot. `res` is the eight
    doublewords of the context's `result.offset` and `result.size` (at
    `ctx + 184` and `ctx + 216`), `fr` the ten doublewords at `fbase`. -/
def exitFrame (E : ExitEnv) (a1v g0 s2 st0 : Word) (res fr : List Word) : Assertion :=
  (.x10 ↦ᵣ E.ctx) ** (.x11 ↦ᵣ a1v) ** (.x8 ↦ᵣ E.c0) ** (.x9 ↦ᵣ E.c1) ** (.x18 ↦ᵣ E.c2) **
  (.x19 ↦ᵣ E.c3) ** (.x20 ↦ᵣ E.c4) ** (.x21 ↦ᵣ E.c5) ** (.x22 ↦ᵣ E.c6) ** (.x23 ↦ᵣ E.c7) **
  (.x24 ↦ᵣ E.c8) ** (.x25 ↦ᵣ E.c9) ** (.x26 ↦ᵣ E.c10) ** (.x27 ↦ᵣ E.c11) **
  ((E.ctx + 8) ↦ₘ g0) ** ((E.ctx + 304) ↦ₘ E.jb) ** (E.slot2 ↦ₘ s2) ** ((E.ctx + 248) ↦ₘ st0) **
  (E.jb ↦ₘ E.v0) ** ((E.jb + 8) ↦ₘ E.v1) ** ((E.jb + 16) ↦ₘ E.v2) ** ((E.jb + 24) ↦ₘ E.v3) **
  ((E.jb + 32) ↦ₘ E.v4) ** ((E.jb + 40) ↦ₘ E.v5) ** ((E.jb + 48) ↦ₘ E.v6) **
  ((E.jb + 56) ↦ₘ E.v7) ** ((E.jb + 64) ↦ₘ E.v8) ** ((E.jb + 72) ↦ₘ E.v9) **
  ((E.jb + 80) ↦ₘ E.v10) ** ((E.jb + 88) ↦ₘ E.v11) ** ((E.jb + 96) ↦ₘ E.v12) **
  ((E.jb + 104) ↦ₘ E.v13) ** words (E.ctx + 184) res ** words E.fbase fr

/-- The machine at the `setjmp` return site after the interpreter halted with
    `status` in the context's status field, `g` in its gas field and `res` in
    its `result.offset` and `result.size` fields. The remaining arguments are
    leftovers no later code depends on. -/
def final (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word) (j12 j13 j14 js2 : Word)
    (status g : Word) (res fr : List Word) : Assertion :=
  (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ E.v0) ** (.x2 ↦ᵣ E.v13) ** (.x10 ↦ᵣ 1) **
  (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x001#12)) ** (.x12 ↦ᵣ j12) ** (.x13 ↦ᵣ j13) **
  (.x14 ↦ᵣ j14) ** (.x15 ↦ᵣ E.ctx) ** (.x16 ↦ᵣ scr.r16) ** (.x17 ↦ᵣ scr.r17) **
  (.x5 ↦ᵣ scr.r5) ** (.x6 ↦ᵣ scr.r6) ** (.x7 ↦ᵣ scr.r7) ** (.x28 ↦ᵣ scr.r28) ** (.x29 ↦ᵣ scr.r29) **
  (.x30 ↦ᵣ scr.r30) ** (.x31 ↦ᵣ scr.r31) ** (.x8 ↦ᵣ E.v1) ** (.x9 ↦ᵣ E.v2) ** (.x18 ↦ᵣ E.v3) **
  (.x19 ↦ᵣ E.v4) ** (.x20 ↦ᵣ E.v5) ** (.x21 ↦ᵣ E.v6) ** (.x22 ↦ᵣ E.v7) ** (.x23 ↦ᵣ E.v8) **
  (.x24 ↦ᵣ E.v9) ** (.x25 ↦ᵣ E.v10) ** (.x26 ↦ᵣ E.v11) ** (.x27 ↦ᵣ E.v12) **
  (frameSlot L.sp ↦ₘ scr.slot) ** words L.bottom limbs ** bytesRegion L.codeBase L.code **
  words L.tbl L.table ** ((E.ctx + 8) ↦ₘ g) ** ((E.ctx + 304) ↦ₘ E.jb) ** (E.slot2 ↦ₘ js2) **
  ((E.ctx + 248) ↦ₘ status) ** (E.jb ↦ₘ E.v0) ** ((E.jb + 8) ↦ₘ E.v1) ** ((E.jb + 16) ↦ₘ E.v2) **
  ((E.jb + 24) ↦ₘ E.v3) ** ((E.jb + 32) ↦ₘ E.v4) ** ((E.jb + 40) ↦ₘ E.v5) **
  ((E.jb + 48) ↦ₘ E.v6) ** ((E.jb + 56) ↦ₘ E.v7) ** ((E.jb + 64) ↦ₘ E.v8) **
  ((E.jb + 72) ↦ₘ E.v9) ** ((E.jb + 80) ↦ₘ E.v10) ** ((E.jb + 88) ↦ₘ E.v11) **
  ((E.jb + 96) ↦ₘ E.v12) ** ((E.jb + 104) ↦ₘ E.v13) ** words (E.ctx + 184) res **
  words E.fbase fr

/-- STOP: from the invariant to the `setjmp` return site, with status 0 and
    the remaining gas stored in the context. -/
theorem stop_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hcs : ∀ a i, CodeReq.ofProg base Image.f_stop.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 16 + signExtend21 0x00acb8#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2) :
    cpsTripleWithin 29 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas) (base + 16 + 4) ((0 : Word) + signExtend12 0x000#12)
        (BitVec.ofNat 64 gas) res fr) := by
  have h1 := stop_spec base L.sp L.ra E.ctx (BitVec.ofNat 64 gas) a1v g0 scr.slot (E.ctx + 8)
    (frameSlot L.sp) (by rw [se_lit_8]) rfl
  rw [h_be] at h1
  have h2 := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 16 + 4)
    ((0 : Word) + signExtend12 0x000#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h1 := cpsTripleWithin_extend_code hcs h1
  unfold interp exitFrame final
  runBlock h1 h2

end PureInterp.Machine
