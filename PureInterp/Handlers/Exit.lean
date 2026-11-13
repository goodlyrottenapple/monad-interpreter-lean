import PureInterp.Handlers.Add

/-!
# The exit path: STOP, `Context::exit`, `longjmp`

A handler that halts stores the remaining gas, calls
`runtime::Context::exit(status)`, which records the status and `longjmp`s to
the buffer the trampoline set up. Each function is proved over its own code;
`stop_exit_spec` links the three over any code requirement that contains them.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-! ## `longjmp` -/

theorem longjmp_body (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 oI : BitVec 12)
    (base jb v r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Word) :
    cpsTripleWithin 16 base (base + 64) (CodeReq.ofProg base [
      .LD .x1 .x10 k0, .LD .x8 .x10 k1, .LD .x9 .x10 k2, .LD .x18 .x10 k3, .LD .x19 .x10 k4, .LD .x20 .x10 k5, .LD .x21 .x10 k6, .LD .x22 .x10 k7, .LD .x23 .x10 k8, .LD .x24 .x10 k9, .LD .x25 .x10 k10, .LD .x26 .x10 k11, .LD .x27 .x10 k12, .LD .x2 .x10 k13,
      .SLTIU .x10 .x11 oI, .ADD .x10 .x10 .x11])
      ((.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) **
       (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) **
       (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x10 ↦ᵣ jb) **
       (.x11 ↦ᵣ v) ** ((jb + signExtend12 k0) ↦ₘ v0) ** ((jb + signExtend12 k1) ↦ₘ v1) **
       ((jb + signExtend12 k2) ↦ₘ v2) ** ((jb + signExtend12 k3) ↦ₘ v3) **
       ((jb + signExtend12 k4) ↦ₘ v4) ** ((jb + signExtend12 k5) ↦ₘ v5) **
       ((jb + signExtend12 k6) ↦ₘ v6) ** ((jb + signExtend12 k7) ↦ₘ v7) **
       ((jb + signExtend12 k8) ↦ₘ v8) ** ((jb + signExtend12 k9) ↦ₘ v9) **
       ((jb + signExtend12 k10) ↦ₘ v10) ** ((jb + signExtend12 k11) ↦ₘ v11) **
       ((jb + signExtend12 k12) ↦ₘ v12) ** ((jb + signExtend12 k13) ↦ₘ v13))
      ((.x1 ↦ᵣ v0) ** (.x8 ↦ᵣ v1) ** (.x9 ↦ᵣ v2) ** (.x18 ↦ᵣ v3) ** (.x19 ↦ᵣ v4) **
       (.x20 ↦ᵣ v5) ** (.x21 ↦ᵣ v6) ** (.x22 ↦ᵣ v7) ** (.x23 ↦ᵣ v8) ** (.x24 ↦ᵣ v9) **
       (.x25 ↦ᵣ v10) ** (.x26 ↦ᵣ v11) ** (.x27 ↦ᵣ v12) ** (.x2 ↦ᵣ v13) **
       (.x10 ↦ᵣ ((if BitVec.ult v (signExtend12 oI) then (1 : Word) else 0) + v)) **
       (.x11 ↦ᵣ v) ** ((jb + signExtend12 k0) ↦ₘ v0) ** ((jb + signExtend12 k1) ↦ₘ v1) **
       ((jb + signExtend12 k2) ↦ₘ v2) ** ((jb + signExtend12 k3) ↦ₘ v3) **
       ((jb + signExtend12 k4) ↦ₘ v4) ** ((jb + signExtend12 k5) ↦ₘ v5) **
       ((jb + signExtend12 k6) ↦ₘ v6) ** ((jb + signExtend12 k7) ↦ₘ v7) **
       ((jb + signExtend12 k8) ↦ₘ v8) ** ((jb + signExtend12 k9) ↦ₘ v9) **
       ((jb + signExtend12 k10) ↦ₘ v10) ** ((jb + signExtend12 k11) ↦ₘ v11) **
       ((jb + signExtend12 k12) ↦ₘ v12) ** ((jb + signExtend12 k13) ↦ₘ v13)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `longjmp(jb, v)`: restore `ra`, `s0`–`s11`, `sp` from the buffer and return
    to the saved `ra` with `a0 = v` (or 1 if `v = 0`). -/
theorem longjmp_spec (base jb v r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 : Word)
    (h_j0 : jb + signExtend12 0x000#12 = j0)
    (h_j1 : jb + signExtend12 0x008#12 = j1)
    (h_j2 : jb + signExtend12 0x010#12 = j2)
    (h_j3 : jb + signExtend12 0x018#12 = j3)
    (h_j4 : jb + signExtend12 0x020#12 = j4)
    (h_j5 : jb + signExtend12 0x028#12 = j5)
    (h_j6 : jb + signExtend12 0x030#12 = j6)
    (h_j7 : jb + signExtend12 0x038#12 = j7)
    (h_j8 : jb + signExtend12 0x040#12 = j8)
    (h_j9 : jb + signExtend12 0x048#12 = j9)
    (h_j10 : jb + signExtend12 0x050#12 = j10)
    (h_j11 : jb + signExtend12 0x058#12 = j11)
    (h_j12 : jb + signExtend12 0x060#12 = j12)
    (h_j13 : jb + signExtend12 0x068#12 = j13) :
    cpsTripleWithin 17 base ((v0 + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_longjmp.prog)
      ((.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) **
       (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) **
       (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x10 ↦ᵣ jb) **
       (.x11 ↦ᵣ v) ** (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) ** (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) **
       (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) ** (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) **
       (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13))
      ((.x1 ↦ᵣ v0) ** (.x8 ↦ᵣ v1) ** (.x9 ↦ᵣ v2) ** (.x18 ↦ᵣ v3) ** (.x19 ↦ᵣ v4) **
       (.x20 ↦ᵣ v5) ** (.x21 ↦ᵣ v6) ** (.x22 ↦ᵣ v7) ** (.x23 ↦ᵣ v8) ** (.x24 ↦ᵣ v9) **
       (.x25 ↦ᵣ v10) ** (.x26 ↦ᵣ v11) ** (.x27 ↦ᵣ v12) ** (.x2 ↦ᵣ v13) **
       (.x10 ↦ᵣ ((if BitVec.ult v (signExtend12 0x001#12) then (1 : Word) else 0) + v)) **
       (.x11 ↦ᵣ v) ** (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) ** (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) **
       (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) ** (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) **
       (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13)) := by
  have hb := longjmp_body 0x000#12 0x008#12 0x010#12 0x018#12 0x020#12 0x028#12 0x030#12 0x038#12 0x040#12 0x048#12 0x050#12 0x058#12 0x060#12 0x068#12 0x001#12 base jb v r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  rw [h_j0, h_j1, h_j2, h_j3, h_j4, h_j5, h_j6, h_j7, h_j8, h_j9, h_j10, h_j11, h_j12, h_j13] at hb
  have hj := jalr_x0_spec_gen_within .x1 v0 0x000#12 (base + 64)
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_longjmp.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_longjmp.prog 16 (base + 64) (by decide) (by decide) (by rfl))) hj
  runBlock hb hj

/-! ## `Context::exit` -/

theorem exit_body (oF oM oJ oS oSt oOne : BitVec 12) (base sp ra ctx st r15 jb slot st0 : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .ADDI .x15 .x10 oM, .LD .x10 .x10 oJ, .SD .x2 .x1 oS,
      .SD .x15 .x11 oSt, .ADDI .x11 .x0 oOne])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ st) ** (.x15 ↦ᵣ r15) **
       ((ctx + signExtend12 oJ) ↦ₘ jb) ** ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ slot) **
       ((ctx + signExtend12 oM + signExtend12 oSt) ↦ₘ st0))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) ** (.x10 ↦ᵣ jb) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 oOne)) ** (.x15 ↦ᵣ (ctx + signExtend12 oM)) **
       ((ctx + signExtend12 oJ) ↦ₘ jb) ** ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ ra) **
       ((ctx + signExtend12 oM + signExtend12 oSt) ↦ₘ st)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `Context::exit(status)` up to its call of `longjmp`: record the status in
    the context and load the jump buffer pointer. -/
theorem exit_spec (base sp ra ctx st r15 jb slot st0 jcell scell stcell : Word)
    (h_jcell : ctx + signExtend12 0x130#12 = jcell)
    (h_scell : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell)
    (h_stcell : ctx + signExtend12 0x000#12 + signExtend12 0x0f8#12 = stcell) :
    cpsTripleWithin 7 base (base + 24 + signExtend21 0x000044#21)
      (CodeReq.ofProg base Image.f_rt_Context_exit.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ st) ** (.x15 ↦ᵣ r15) **
       (jcell ↦ₘ jb) ** (scell ↦ₘ slot) ** (stcell ↦ₘ st0))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (base + 24 + 4)) ** (.x2 ↦ᵣ (sp + signExtend12 0xff0#12)) **
       (.x10 ↦ᵣ jb) ** (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x001#12)) **
       (.x15 ↦ᵣ (ctx + signExtend12 0x000#12)) **
       (jcell ↦ₘ jb) ** (scell ↦ₘ ra) ** (stcell ↦ₘ st)) := by
  have hb := exit_body 0xff0#12 0x000#12 0x130#12 0x008#12 0x0f8#12 0x001#12 base sp ra ctx st r15 jb slot st0
  rw [h_jcell, h_scell, h_stcell] at hb
  have hj := jal_spec_within .x1 ra 0x000044#21 (base + 24) (by decide)
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_rt_Context_exit.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_exit.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hj
  runBlock hb hj

/-! ## STOP -/

theorem stop_body (oF oZ oG oS : BitVec 12) (base sp ra ctx gas r11 g0 slot : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .ADDI .x11 .x0 oZ, .SD .x10 .x14 oG, .SD .x2 .x1 oS])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ r11) ** (.x14 ↦ᵣ gas) **
       ((ctx + signExtend12 oG) ↦ₘ g0) ** ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ slot))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) ** (.x10 ↦ᵣ ctx) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 oZ)) ** (.x14 ↦ᵣ gas) **
       ((ctx + signExtend12 oG) ↦ₘ gas) ** ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ ra)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The STOP handler up to its call of `Context::exit`: store the remaining
    gas in the context and pass status 0. -/
theorem stop_spec (base sp ra ctx gas r11 g0 slot gcell scell : Word)
    (h_gcell : ctx + signExtend12 0x008#12 = gcell)
    (h_scell : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell) :
    cpsTripleWithin 5 base (base + 16 + signExtend21 0x00acb8#21)
      (CodeReq.ofProg base Image.f_stop.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ r11) ** (.x14 ↦ᵣ gas) **
       (gcell ↦ₘ g0) ** (scell ↦ₘ slot))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (base + 16 + 4)) ** (.x2 ↦ᵣ (sp + signExtend12 0xff0#12)) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x000#12)) ** (.x14 ↦ᵣ gas) **
       (gcell ↦ₘ gas) ** (scell ↦ₘ ra)) := by
  have hb := stop_body 0xff0#12 0x000#12 0x008#12 0x008#12 base sp ra ctx gas r11 g0 slot
  rw [h_gcell, h_scell] at hb
  have hj := jal_spec_within .x1 ra 0x00acb8#21 (base + 16) (by decide)
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_stop.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_stop.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hj
  runBlock hb hj

/-! ## The whole STOP exit -/

/-- From the entry of the STOP handler to the `setjmp` return site: the
    remaining gas and status 0 are in the context, the callee-saved registers
    and `sp` are restored from the jump buffer, and `a0 = 1`. -/
theorem stop_exit_spec (cr : CodeReq) (bs be bl ctx gas r11 r15 g0 slot1 slot2 jb st0 : Word)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 gcell scell1 scell2 jcell stcell : Word)
    (hcs : ∀ a i, CodeReq.ofProg bs Image.f_stop.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : bs + 16 + signExtend21 0x00acb8#21 = be)
    (h_bl : be + 24 + signExtend21 0x000044#21 = bl)
    (h_gcell : ctx + signExtend12 0x008#12 = gcell)
    (h_scell1 : r13 + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell1)
    (h_scell2 : (r13 + signExtend12 0xff0#12) + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell2)
    (h_jcell : ctx + signExtend12 0x130#12 = jcell)
    (h_stcell : ctx + signExtend12 0x000#12 + signExtend12 0x0f8#12 = stcell)
    (h_j0 : jb + signExtend12 0x000#12 = j0)
    (h_j1 : jb + signExtend12 0x008#12 = j1)
    (h_j2 : jb + signExtend12 0x010#12 = j2)
    (h_j3 : jb + signExtend12 0x018#12 = j3)
    (h_j4 : jb + signExtend12 0x020#12 = j4)
    (h_j5 : jb + signExtend12 0x028#12 = j5)
    (h_j6 : jb + signExtend12 0x030#12 = j6)
    (h_j7 : jb + signExtend12 0x038#12 = j7)
    (h_j8 : jb + signExtend12 0x040#12 = j8)
    (h_j9 : jb + signExtend12 0x048#12 = j9)
    (h_j10 : jb + signExtend12 0x050#12 = j10)
    (h_j11 : jb + signExtend12 0x058#12 = j11)
    (h_j12 : jb + signExtend12 0x060#12 = j12)
    (h_j13 : jb + signExtend12 0x068#12 = j13) :
    cpsTripleWithin 29 bs ((v0 + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) **
       (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) **
       (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x0 ↦ᵣ 0) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ r11) ** (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ r15) ** (gcell ↦ₘ g0) **
       (scell1 ↦ₘ slot1) ** (jcell ↦ₘ jb) ** (scell2 ↦ₘ slot2) ** (stcell ↦ₘ st0) ** (j0 ↦ₘ v0) **
       (j1 ↦ₘ v1) ** (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) **
       (j7 ↦ₘ v7) ** (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) **
       (j13 ↦ₘ v13))
      ((.x1 ↦ᵣ v0) ** (.x8 ↦ᵣ v1) ** (.x9 ↦ᵣ v2) ** (.x18 ↦ᵣ v3) ** (.x19 ↦ᵣ v4) **
       (.x20 ↦ᵣ v5) ** (.x21 ↦ᵣ v6) ** (.x22 ↦ᵣ v7) ** (.x23 ↦ᵣ v8) ** (.x24 ↦ᵣ v9) **
       (.x25 ↦ᵣ v10) ** (.x26 ↦ᵣ v11) ** (.x27 ↦ᵣ v12) ** (.x2 ↦ᵣ v13) ** (.x0 ↦ᵣ 0) **
       (.x10 ↦ᵣ ((if BitVec.ult ((0 : Word) + signExtend12 0x001#12) (signExtend12 0x001#12) then (1 : Word) else 0) + ((0 : Word) + signExtend12 0x001#12))) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x001#12)) ** (.x14 ↦ᵣ gas) **
       (.x15 ↦ᵣ (ctx + signExtend12 0x000#12)) ** (gcell ↦ₘ gas) ** (scell1 ↦ₘ r0) **
       (jcell ↦ₘ jb) ** (scell2 ↦ₘ (bs + 16 + 4)) **
       (stcell ↦ₘ ((0 : Word) + signExtend12 0x000#12)) ** (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) **
       (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) **
       (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13)) := by
  have h1 := stop_spec bs r13 r0 ctx gas r11 g0 slot1 gcell scell1 h_gcell h_scell1
  rw [h_be] at h1
  have h2 := exit_spec be (r13 + signExtend12 0xff0#12) (bs + 16 + 4) ctx ((0 : Word) + signExtend12 0x000#12) r15 jb slot2 st0
    jcell scell2 stcell h_jcell h_scell2 h_stcell
  rw [h_bl] at h2
  have h3 := longjmp_spec bl jb ((0 : Word) + signExtend12 0x001#12)
    (be + 24 + 4) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 ((r13 + signExtend12 0xff0#12) + signExtend12 0xff0#12)
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 h_j0 h_j1 h_j2 h_j3 h_j4 h_j5 h_j6 h_j7 h_j8 h_j9 h_j10 h_j11 h_j12 h_j13
  have h1 := cpsTripleWithin_extend_code hcs h1
  have h2 := cpsTripleWithin_extend_code hce h2
  have h3 := cpsTripleWithin_extend_code hcl h3
  runBlock h1 h2 h3

end PureInterp.Handlers
