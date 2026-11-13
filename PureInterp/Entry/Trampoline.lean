import PureInterp.Entry.Basic

/-!
# `trampoline`

`trampoline(ctx, icode, stack, fn)` spills its arguments, calls
`setjmp(sp + 32)`, and
* when `setjmp` returns 0: stores the jump buffer pointer in the context
  (`ctx + 0x130`) and calls `fn(_, ctx, icode, stack, _)` (`fn` is `core_loop`);
* when it returns non-zero (through `longjmp`): pops its frame and returns.

Three theorems: `trampoline_enter` (entry to the call of `setjmp`),
`trampoline_call` (from the return site with `a0 = 0` to the entry of `fn`),
`trampoline_leave` (from the return site with `a0 ≠ 0` to the return).
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem tramp_spill (oF oC oJ oR oFn oI oS : BitVec 12)
    (base sp ra ctx ic stk fn s0 s1 s2 s3 s4 : Word) :
    cpsTripleWithin 7 base (base + 28) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .SD .x2 .x10 oC, .ADDI .x10 .x2 oJ, .SD .x2 .x1 oR,
      .SD .x2 .x13 oFn, .SD .x2 .x11 oI, .SD .x2 .x12 oS])
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) **
       (.x13 ↦ᵣ fn) **
       ((sp + signExtend12 oF + signExtend12 oC) ↦ₘ s0) **
       ((sp + signExtend12 oF + signExtend12 oR) ↦ₘ s1) **
       ((sp + signExtend12 oF + signExtend12 oFn) ↦ₘ s2) **
       ((sp + signExtend12 oF + signExtend12 oI) ↦ₘ s3) **
       ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ s4))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) **
       (.x10 ↦ᵣ (sp + signExtend12 oF + signExtend12 oJ)) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) **
       (.x13 ↦ᵣ fn) **
       ((sp + signExtend12 oF + signExtend12 oC) ↦ₘ ctx) **
       ((sp + signExtend12 oF + signExtend12 oR) ↦ₘ ra) **
       ((sp + signExtend12 oF + signExtend12 oFn) ↦ₘ fn) **
       ((sp + signExtend12 oF + signExtend12 oI) ↦ₘ ic) **
       ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ stk)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Entry of `trampoline` up to its call of `setjmp`: the frame holds the four
    arguments and `ra`; `a0` points at the jump buffer `sp - 256 + 32`. -/
theorem trampoline_enter (base sp ra ctx ic stk fn s0 s1 s2 s3 s4 : Word)
    (cslot rslot fslot islot sslot : Word)
    (h_cslot : sp + signExtend12 0xf00#12 + signExtend12 0x000#12 = cslot)
    (h_rslot : sp + signExtend12 0xf00#12 + signExtend12 0x0f8#12 = rslot)
    (h_fslot : sp + signExtend12 0xf00#12 + signExtend12 0x008#12 = fslot)
    (h_islot : sp + signExtend12 0xf00#12 + signExtend12 0x010#12 = islot)
    (h_sslot : sp + signExtend12 0xf00#12 + signExtend12 0x018#12 = sslot) :
    cpsTripleWithin 8 base (base + 28 + signExtend21 0x00128c#21)
      (CodeReq.ofProg base Image.f_trampoline.prog)
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) **
       (.x13 ↦ᵣ fn) ** (cslot ↦ₘ s0) ** (rslot ↦ₘ s1) ** (fslot ↦ₘ s2) ** (islot ↦ₘ s3) **
       (sslot ↦ₘ s4))
      ((.x1 ↦ᵣ (base + 28 + 4)) ** (.x2 ↦ᵣ (sp + signExtend12 0xf00#12)) **
       (.x10 ↦ᵣ (sp + signExtend12 0xf00#12 + signExtend12 0x020#12)) ** (.x11 ↦ᵣ ic) **
       (.x12 ↦ᵣ stk) ** (.x13 ↦ᵣ fn) ** (cslot ↦ₘ ctx) ** (rslot ↦ₘ ra) ** (fslot ↦ₘ fn) **
       (islot ↦ₘ ic) ** (sslot ↦ₘ stk)) := by
  have hb := tramp_spill 0xf00#12 0x000#12 0x020#12 0x0f8#12 0x008#12 0x010#12 0x018#12
    base sp ra ctx ic stk fn s0 s1 s2 s3 s4
  rw [h_cslot, h_rslot, h_fslot, h_islot, h_sslot] at hb
  have hj := jal_spec_within .x1 ra 0x00128c#21 (base + 28) (by decide)
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_trampoline.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_trampoline.prog 7 (base + 28) (by decide) (by decide) (by rfl))) hj
  runBlock hb hj

theorem tramp_setup (oC oJ oS oB oI oFn oM oZ : BitVec 12)
    (base sp r11 r12 r13 r14 r15 ctx ic stk fn jb0 : Word) :
    cpsTripleWithin 8 base (base + 32) (CodeReq.ofProg base [
      .LD .x14 .x2 oC, .ADDI .x15 .x2 oJ, .LD .x13 .x2 oS, .SD .x14 .x15 oB,
      .LD .x12 .x2 oI, .LD .x15 .x2 oFn, .ADDI .x11 .x14 oM, .ADDI .x14 .x0 oZ])
      ((.x0 ↦ᵣ 0) ** (.x2 ↦ᵣ sp) ** (.x11 ↦ᵣ r11) ** (.x12 ↦ᵣ r12) ** (.x13 ↦ᵣ r13) **
       (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       ((sp + signExtend12 oC) ↦ₘ ctx) ** ((sp + signExtend12 oS) ↦ₘ stk) **
       ((sp + signExtend12 oI) ↦ₘ ic) ** ((sp + signExtend12 oFn) ↦ₘ fn) **
       ((ctx + signExtend12 oB) ↦ₘ jb0))
      ((.x0 ↦ᵣ 0) ** (.x2 ↦ᵣ sp) ** (.x11 ↦ᵣ (ctx + signExtend12 oM)) ** (.x12 ↦ᵣ ic) **
       (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ ((0 : Word) + signExtend12 oZ)) ** (.x15 ↦ᵣ fn) **
       ((sp + signExtend12 oC) ↦ₘ ctx) ** ((sp + signExtend12 oS) ↦ₘ stk) **
       ((sp + signExtend12 oI) ↦ₘ ic) ** ((sp + signExtend12 oFn) ↦ₘ fn) **
       ((ctx + signExtend12 oB) ↦ₘ (sp + signExtend12 oJ))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `setjmp` returned 0: record the jump buffer in the context and call `fn`
    with `a1 = ctx`, `a2 = icode`, `a3 = stack`; `ra` is the return site
    `base + 72`. `sp` is the trampoline's frame pointer here. -/
theorem trampoline_call (base sp r1 a0 r11 r12 r13 r14 r15 ctx ic stk fn jb0 : Word)
    (cslot fslot islot sslot jcell : Word)
    (ha0 : a0 = 0)
    (h_cslot : sp + signExtend12 0x000#12 = cslot)
    (h_fslot : sp + signExtend12 0x008#12 = fslot)
    (h_islot : sp + signExtend12 0x010#12 = islot)
    (h_sslot : sp + signExtend12 0x018#12 = sslot)
    (h_jcell : ctx + signExtend12 0x130#12 = jcell) :
    cpsTripleWithin 10 (base + 32) ((fn + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_trampoline.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ r11) **
       (.x12 ↦ᵣ r12) ** (.x13 ↦ᵣ r13) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (cslot ↦ₘ ctx) ** (sslot ↦ₘ stk) ** (islot ↦ₘ ic) ** (fslot ↦ₘ fn) ** (jcell ↦ₘ jb0))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (base + 68 + 4)) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) **
       (.x11 ↦ᵣ (ctx + signExtend12 0x000#12)) ** (.x12 ↦ᵣ ic) ** (.x13 ↦ᵣ stk) **
       (.x14 ↦ᵣ ((0 : Word) + signExtend12 0x000#12)) ** (.x15 ↦ᵣ fn) **
       (cslot ↦ₘ ctx) ** (sslot ↦ₘ stk) ** (islot ↦ₘ ic) ** (fslot ↦ₘ fn) **
       (jcell ↦ₘ (sp + signExtend12 0x020#12))) := by
  have hbne := cpsBranchWithin_ntakenStripPure2
    (bne_spec_gen_within .x10 .x0 0x0028#13 a0 0 (base + 32))
    (fun hp hq => (pure_end2 hp hq) ha0)
  have hb := tramp_setup 0x000#12 0x020#12 0x018#12 0x130#12 0x010#12 0x008#12 0x000#12 0x000#12
    (base + 36) sp r11 r12 r13 r14 r15 ctx ic stk fn jb0
  rw [h_cslot, h_fslot, h_islot, h_sslot, h_jcell] at hb
  have hj := jalr_spec_within .x1 .x15 fn r1 0x000#12 (base + 68) (by decide)
  have hbne := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_trampoline.prog 8 (base + 32) (by decide) (by decide) (by rfl))) hbne
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 36) Image.f_trampoline.prog _ 9 (by rfl) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_trampoline.prog 17 (base + 68) (by decide) (by decide) (by rfl))) hj
  runBlock hbne hb hj

theorem tramp_pop (oR oF : BitVec 12) (base sp r1 ra : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .LD .x1 .x2 oR, .ADDI .x2 .x2 oF])
      ((.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ sp) ** ((sp + signExtend12 oR) ↦ₘ ra))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) ** ((sp + signExtend12 oR) ↦ₘ ra)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `setjmp` returned non-zero (the `longjmp` from `Context::exit`): pop the
    frame and return to the caller of `trampoline`. -/
theorem trampoline_leave (base sp r1 a0 ra rslot : Word)
    (ha0 : a0 ≠ 0)
    (h_rslot : sp + signExtend12 0x0f8#12 = rslot) :
    cpsTripleWithin 4 (base + 32) ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_trampoline.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (rslot ↦ₘ ra))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 0x100#12)) ** (.x10 ↦ᵣ a0) **
       (rslot ↦ₘ ra)) := by
  have hbne := cpsBranchWithin_takenStripPure2
    (bne_spec_gen_within .x10 .x0 0x0028#13 a0 0 (base + 32))
    (fun hp hq => ha0 (pure_end2 hp hq))
  have e : base + 32 + signExtend13 0x0028#13 = base + 72 := by rv64_addr
  rw [e] at hbne
  have hb := tramp_pop 0x0f8#12 0x100#12 (base + 72) sp r1 ra
  rw [h_rslot] at hb
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 80)
  have hbne := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_trampoline.prog 8 (base + 32) (by decide) (by decide) (by rfl))) hbne
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 72) Image.f_trampoline.prog _ 18 (by rfl) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_trampoline.prog 20 (base + 80) (by decide) (by decide) (by rfl))) hj
  runBlock hbne hb hj

end PureInterp.Entry
