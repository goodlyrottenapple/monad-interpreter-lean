import RiscvZkvm.Rv64.Logic
import PureInterp.Image.Index

/-!
# `setjmp`

The mirror of `longjmp`: store `ra`, `s0`–`s11`, `sp` into the buffer at `a0`
and return 0. (The second return, through `longjmp`, is `Handlers.longjmp_spec`.)
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem setjmp_body (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 oZ : BitVec 12)
    (base jb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Word) :
    cpsTripleWithin 15 base (base + 60) (CodeReq.ofProg base [
      .SD .x10 .x1 k0, .SD .x10 .x8 k1, .SD .x10 .x9 k2, .SD .x10 .x18 k3, .SD .x10 .x19 k4, .SD .x10 .x20 k5, .SD .x10 .x21 k6, .SD .x10 .x22 k7, .SD .x10 .x23 k8, .SD .x10 .x24 k9, .SD .x10 .x25 k10, .SD .x10 .x26 k11, .SD .x10 .x27 k12, .SD .x10 .x2 k13,
      .ADDI .x10 .x0 oZ])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) ** (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) ** (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x10 ↦ᵣ jb) **
       ((jb + signExtend12 k0) ↦ₘ v0) ** ((jb + signExtend12 k1) ↦ₘ v1) ** ((jb + signExtend12 k2) ↦ₘ v2) ** ((jb + signExtend12 k3) ↦ₘ v3) ** ((jb + signExtend12 k4) ↦ₘ v4) ** ((jb + signExtend12 k5) ↦ₘ v5) ** ((jb + signExtend12 k6) ↦ₘ v6) ** ((jb + signExtend12 k7) ↦ₘ v7) ** ((jb + signExtend12 k8) ↦ₘ v8) ** ((jb + signExtend12 k9) ↦ₘ v9) ** ((jb + signExtend12 k10) ↦ₘ v10) ** ((jb + signExtend12 k11) ↦ₘ v11) ** ((jb + signExtend12 k12) ↦ₘ v12) ** ((jb + signExtend12 k13) ↦ₘ v13))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) ** (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) ** (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 oZ)) **
       ((jb + signExtend12 k0) ↦ₘ r0) ** ((jb + signExtend12 k1) ↦ₘ r1) ** ((jb + signExtend12 k2) ↦ₘ r2) ** ((jb + signExtend12 k3) ↦ₘ r3) ** ((jb + signExtend12 k4) ↦ₘ r4) ** ((jb + signExtend12 k5) ↦ₘ r5) ** ((jb + signExtend12 k6) ↦ₘ r6) ** ((jb + signExtend12 k7) ↦ₘ r7) ** ((jb + signExtend12 k8) ↦ₘ r8) ** ((jb + signExtend12 k9) ↦ₘ r9) ** ((jb + signExtend12 k10) ↦ₘ r10) ** ((jb + signExtend12 k11) ↦ₘ r11) ** ((jb + signExtend12 k12) ↦ₘ r12) ** ((jb + signExtend12 k13) ↦ₘ r13)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `setjmp(jb)`: save `ra`, `s0`–`s11`, `sp` (`r0`…`r13`) in the buffer and
    return to `ra` with `a0 = 0`. -/
theorem setjmp_spec (base jb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 : Word)
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
    cpsTripleWithin 16 base ((r0 + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_setjmp.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) ** (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) ** (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x10 ↦ᵣ jb) **
       (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) ** (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) ** (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) ** (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) ** (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 0x000#12)) **
       (j0 ↦ₘ r0) ** (j1 ↦ₘ r1) ** (j2 ↦ₘ r2) ** (j3 ↦ₘ r3) ** (j4 ↦ₘ r4) ** (j5 ↦ₘ r5) ** (j6 ↦ₘ r6) ** (j7 ↦ₘ r7) ** (j8 ↦ₘ r8) ** (j9 ↦ₘ r9) ** (j10 ↦ₘ r10) ** (j11 ↦ₘ r11) ** (j12 ↦ₘ r12) ** (j13 ↦ₘ r13)) := by
  have hb := setjmp_body 0x000#12 0x008#12 0x010#12 0x018#12 0x020#12 0x028#12 0x030#12 0x038#12 0x040#12 0x048#12 0x050#12 0x058#12 0x060#12 0x068#12 0x000#12 base jb r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  rw [h_j0, h_j1, h_j2, h_j3, h_j4, h_j5, h_j6, h_j7, h_j8, h_j9, h_j10, h_j11, h_j12, h_j13] at hb
  have hj := jalr_x0_spec_gen_within .x1 r0 0x000#12 (base + 60)
  have hb := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_setjmp.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hb
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_setjmp.prog 15 (base + 60) (by decide) (by decide) (by rfl))) hj
  runBlock hb hj

end PureInterp.Entry
