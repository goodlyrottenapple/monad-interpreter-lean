import PureInterp.Handlers.Memmove
import PureInterp.Handlers.Exit

/-!
# The RETURN handler

`return_<Cancun>` checks that two operands are present and calls
`return_impl(Success, ctx, stack_top, gas)`, which copies the top word
(offset) and the one below it (size) into the context's `result.offset` and
`result.size` with two `memmove(·, ·, 32)` calls, stores the gas and calls
`Context::exit`. No gas is charged here: memory expansion for the returned
range is charged later, in `Context::copy_result_data`.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64 PureInterp.Machine

theorem add_se0 (x : Word) : x + signExtend12 0x000#12 = x := by
  have : signExtend12 0x000#12 = (0 : Word) := by decide
  rw [this]; exact BitVec.add_zero x

theorem li_32 : (0 : Word) + signExtend12 0x020#12 = BitVec.ofNat 64 32 := by decide

theorem three_slots (t : Word) :
    t + signExtend12 0xfe0#12 + signExtend12 0xfe0#12 + signExtend12 0xfe0#12 =
      t + signExtend12 0xfa0#12 := by
  have : signExtend12 0xfe0#12 + signExtend12 0xfe0#12 + signExtend12 0xfe0#12 =
      (signExtend12 0xfa0#12 : Word) := by decide
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (signExtend12 0xfe0#12), this]

theorem two_slots_ne (t : Word) :
    t + signExtend12 0xfe0#12 + signExtend12 0xfe0#12 ≠ t + signExtend12 0xfa0#12 := by
  intro h
  rw [BitVec.add_assoc] at h
  have h' := (BitVec.add_right_inj t).mp h
  exact absurd h' (by decide)

set_option maxRecDepth 100000

/-! ## `return_impl` -/

theorem ri_pro (oF oA oB k0 k1 k3 k4 k5 k6 k7 k8 k9 oZ oS oE : BitVec 12)
    (base sp ra st ctx t g r15 c0 c1 c2 c3 c4 c5 q0 q1 q3 q4 q5 q6 q7 q8 q9 : Word) :
    cpsTripleWithin 18 base (base + 72) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .ADDI .x15 .x11 oA, .SD .x2 .x15 k0, .ADDI .x15 .x11 oB,
      .SD .x2 .x8 k8, .SD .x2 .x9 k7, .SD .x2 .x18 k6, .SD .x2 .x19 k5, .SD .x2 .x20 k4,
      .SD .x2 .x21 k3, .SD .x2 .x1 k9, .ADDI .x19 .x11 oZ, .SD .x2 .x15 k1,
      .ADDI .x20 .x10 oZ, .ADDI .x21 .x13 oZ, .ADDI .x8 .x12 oS, .ADDI .x18 .x12 oE,
      .ADDI .x9 .x2 oZ])
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ st) ** (.x11 ↦ᵣ ctx) ** (.x12 ↦ᵣ t) **
       (.x13 ↦ᵣ g) ** (.x15 ↦ᵣ r15) ** (.x8 ↦ᵣ c0) ** (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) **
       (.x19 ↦ᵣ c3) ** (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) **
       ((sp + signExtend12 oF + signExtend12 k0) ↦ₘ q0) **
       ((sp + signExtend12 oF + signExtend12 k1) ↦ₘ q1) **
       ((sp + signExtend12 oF + signExtend12 k3) ↦ₘ q3) **
       ((sp + signExtend12 oF + signExtend12 k4) ↦ₘ q4) **
       ((sp + signExtend12 oF + signExtend12 k5) ↦ₘ q5) **
       ((sp + signExtend12 oF + signExtend12 k6) ↦ₘ q6) **
       ((sp + signExtend12 oF + signExtend12 k7) ↦ₘ q7) **
       ((sp + signExtend12 oF + signExtend12 k8) ↦ₘ q8) **
       ((sp + signExtend12 oF + signExtend12 k9) ↦ₘ q9))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) ** (.x10 ↦ᵣ st) ** (.x11 ↦ᵣ ctx) **
       (.x12 ↦ᵣ t) ** (.x13 ↦ᵣ g) ** (.x15 ↦ᵣ (ctx + signExtend12 oB)) **
       (.x8 ↦ᵣ (t + signExtend12 oS)) ** (.x9 ↦ᵣ (sp + signExtend12 oF + signExtend12 oZ)) **
       (.x18 ↦ᵣ (t + signExtend12 oE)) ** (.x19 ↦ᵣ (ctx + signExtend12 oZ)) **
       (.x20 ↦ᵣ (st + signExtend12 oZ)) ** (.x21 ↦ᵣ (g + signExtend12 oZ)) **
       ((sp + signExtend12 oF + signExtend12 k0) ↦ₘ (ctx + signExtend12 oA)) **
       ((sp + signExtend12 oF + signExtend12 k1) ↦ₘ (ctx + signExtend12 oB)) **
       ((sp + signExtend12 oF + signExtend12 k3) ↦ₘ c5) **
       ((sp + signExtend12 oF + signExtend12 k4) ↦ₘ c4) **
       ((sp + signExtend12 oF + signExtend12 k5) ↦ₘ c3) **
       ((sp + signExtend12 oF + signExtend12 k6) ↦ₘ c2) **
       ((sp + signExtend12 oF + signExtend12 k7) ↦ₘ c1) **
       ((sp + signExtend12 oF + signExtend12 k8) ↦ₘ c0) **
       ((sp + signExtend12 oF + signExtend12 k9) ↦ₘ ra)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ri_it (oL oZ o32 oS : BitVec 12) (base p s d v10 v11 v12 : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .LD .x10 .x9 oL, .ADDI .x11 .x8 oZ, .ADDI .x12 .x0 o32, .ADDI .x8 .x8 oS])
      ((.x0 ↦ᵣ 0) ** (.x9 ↦ᵣ p) ** (.x8 ↦ᵣ s) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** ((p + signExtend12 oL) ↦ₘ d))
      ((.x0 ↦ᵣ 0) ** (.x9 ↦ᵣ p) ** (.x8 ↦ᵣ (s + signExtend12 oS)) ** (.x10 ↦ᵣ d) **
       (.x11 ↦ᵣ (s + signExtend12 oZ)) ** (.x12 ↦ᵣ ((0 : Word) + signExtend12 o32)) **
       ((p + signExtend12 oL) ↦ₘ d)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ri_adv (o : BitVec 12) (base p : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x9 .x9 o])
      (.x9 ↦ᵣ p) (.x9 ↦ᵣ (p + signExtend12 o)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ri_tail (oG oZ : BitVec 12) (base ctx g st v10 v11 g0 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .SD .x19 .x21 oG, .ADDI .x11 .x20 oZ, .ADDI .x10 .x19 oZ])
      ((.x19 ↦ᵣ ctx) ** (.x21 ↦ᵣ g) ** (.x20 ↦ᵣ st) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       ((ctx + signExtend12 oG) ↦ₘ g0))
      ((.x19 ↦ᵣ ctx) ** (.x21 ↦ᵣ g) ** (.x20 ↦ᵣ st) ** (.x10 ↦ᵣ (ctx + signExtend12 oZ)) **
       (.x11 ↦ᵣ (st + signExtend12 oZ)) ** ((ctx + signExtend12 oG) ↦ₘ g)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `return_impl(status, ctx, top, gas)` up to its call of `Context::exit`:
    the two top stack words are copied into `ctx.result.offset` and
    `ctx.result.size`, and the gas is stored. -/
theorem return_impl_spec (cr : CodeReq) (bI bM sp ra st ctx t g r15 c0 c1 c2 c3 c4 c5 v14 : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 o0 o1 o2 o3 z0 z1 z2 z3 : Word)
    (q0 q1 q3 q4 q5 q6 q7 q8 q9 g0 : Word)
    (sp' f0 f1 f3 f4 f5 f6 f7 f8 f9 src1 src2 dst1 dst2 gcell : Word)
    (hcI : ∀ a i, CodeReq.ofProg bI Image.f_return_impl.prog a = some i → cr a = some i)
    (hcM : ∀ a i, CodeReq.ofProg bM Image.f_memmove.prog a = some i → cr a = some i)
    (h_bM : bI + 88 + signExtend21 0x003860#21 = bM)
    (h_ra : (bI + 88 + 4 + signExtend12 0x000#12) &&& ~~~1 = bI + 92)
    (h_sp : sp + signExtend12 0xfb0#12 = sp')
    (h_f0 : sp' + signExtend12 0x000#12 = f0) (h_f1 : sp' + signExtend12 0x008#12 = f1)
    (h_f3 : sp' + signExtend12 0x018#12 = f3) (h_f4 : sp' + signExtend12 0x020#12 = f4)
    (h_f5 : sp' + signExtend12 0x028#12 = f5) (h_f6 : sp' + signExtend12 0x030#12 = f6)
    (h_f7 : sp' + signExtend12 0x038#12 = f7) (h_f8 : sp' + signExtend12 0x040#12 = f8)
    (h_f9 : sp' + signExtend12 0x048#12 = f9)
    (h_src1 : t + signExtend12 0xfe0#12 = src1) (h_src2 : src1 + signExtend12 0xfe0#12 = src2)
    (h_dst1 : ctx + signExtend12 0x0b8#12 = dst1) (h_dst2 : ctx + signExtend12 0x0d8#12 = dst2)
    (h_gcell : ctx + signExtend12 0x008#12 = gcell)
    (hs1a : src1.toNat % 8 = 0) (hs2a : src2.toNat % 8 = 0)
    (hd1a : dst1.toNat % 8 = 0) (hd2a : dst2.toNat % 8 = 0)
    (hs1o : src1.toNat + 32 ≤ 2 ^ 64) (hs2o : src2.toNat + 32 ≤ 2 ^ 64)
    (hd1o : dst1.toNat + 32 ≤ 2 ^ 64) (hd2o : dst2.toNat + 32 ≤ 2 ^ 64)
    (hs1v : ∀ i, i < 32 → isValidByteAccess (src1 + BitVec.ofNat 64 i) = true)
    (hs2v : ∀ i, i < 32 → isValidByteAccess (src2 + BitVec.ofNat 64 i) = true)
    (hd1v : ∀ i, i < 32 → isValidByteAccess (dst1 + BitVec.ofNat 64 i) = true)
    (hd2v : ∀ i, i < 32 → isValidByteAccess (dst2 + BitVec.ofNat 64 i) = true)
    (hlt1 : BitVec.ult src1 dst1) (hlt2 : BitVec.ult src2 dst2) :
    cpsTripleWithin 430 bI (bI + 112 + signExtend21 0x004828#21) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ st) ** (.x11 ↦ᵣ ctx) **
       (.x12 ↦ᵣ t) ** (.x13 ↦ᵣ g) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ r15) ** (.x8 ↦ᵣ c0) **
       (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) ** (.x19 ↦ᵣ c3) ** (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) **
       (f0 ↦ₘ q0) ** (f1 ↦ₘ q1) ** (f3 ↦ₘ q3) ** (f4 ↦ₘ q4) ** (f5 ↦ₘ q5) ** (f6 ↦ₘ q6) **
       (f7 ↦ₘ q7) ** (f8 ↦ₘ q8) ** (f9 ↦ₘ q9) ** (gcell ↦ₘ g0) **
       words src1 [a0, a1, a2, a3] ** words src2 [b0, b1, b2, b3] **
       words dst1 [o0, o1, o2, o3] ** words dst2 [z0, z1, z2, z3])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bI + 112 + 4)) ** (.x2 ↦ᵣ sp') ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ st) **
       (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (.x13 ↦ᵣ g) **
       (.x14 ↦ᵣ ((extractByte b0 0).zeroExtend 64)) ** (.x15 ↦ᵣ (dst2 + BitVec.ofNat 64 0)) **
       (.x8 ↦ᵣ (src2 + signExtend12 0xfe0#12)) **
       (.x9 ↦ᵣ (f0 + signExtend12 0x008#12 + signExtend12 0x008#12)) **
       (.x18 ↦ᵣ (t + signExtend12 0xfa0#12)) ** (.x19 ↦ᵣ ctx) ** (.x20 ↦ᵣ st) ** (.x21 ↦ᵣ g) **
       (f0 ↦ₘ dst1) ** (f1 ↦ₘ dst2) ** (f3 ↦ₘ c5) ** (f4 ↦ₘ c4) ** (f5 ↦ₘ c3) ** (f6 ↦ₘ c2) **
       (f7 ↦ₘ c1) ** (f8 ↦ₘ c0) ** (f9 ↦ₘ ra) ** (gcell ↦ₘ g) **
       words src1 [a0, a1, a2, a3] ** words src2 [b0, b1, b2, b3] **
       words dst1 [a0, a1, a2, a3] ** words dst2 [b0, b1, b2, b3]) := by
  have hf01 : f0 + signExtend12 0x008#12 + signExtend12 0x000#12 = f1 := by
    rw [add_se0, ← h_f0, add_se0, h_f1]
  have hne : src2 ≠ t + signExtend12 0xfa0#12 := by
    rw [← h_src2, ← h_src1]; exact two_slots_ne t
  have heq : src2 + signExtend12 0xfe0#12 = t + signExtend12 0xfa0#12 := by
    rw [← h_src2, ← h_src1]; exact three_slots t
  have hp := ri_pro 0xfb0#12 0x0b8#12 0x0d8#12 0x000#12 0x008#12 0x018#12 0x020#12 0x028#12
    0x030#12 0x038#12 0x040#12 0x048#12 0x000#12 0xfe0#12 0xfa0#12
    bI sp ra st ctx t g r15 c0 c1 c2 c3 c4 c5 q0 q1 q3 q4 q5 q6 q7 q8 q9
  rw [h_sp, h_f0, h_f1, h_f3, h_f4, h_f5, h_f6, h_f7, h_f8, h_f9, h_dst1, h_dst2, h_src1] at hp
  simp only [add_se0] at hp
  have i1 := ri_it 0x000#12 0x000#12 0x020#12 0xfe0#12 (bI + 72) f0 src1 dst1 st ctx t
  rw [h_src2, li_32] at i1
  simp only [add_se0] at i1
  have j1 := jal_spec_within .x1 ra 0x003860#21 (bI + 88) (by decide)
  rw [h_bM] at j1
  have m1 := memmove32 bM dst1 src1 (bI + 88 + 4) v14 dst2 a0 a1 a2 a3 o0 o1 o2 o3
    hs1a hd1a hs1o hd1o hs1v hd1v hlt1
  rw [h_ra] at m1
  have a1' := ri_adv 0x008#12 (bI + 92) f0
  have b1' := cpsBranchWithin_takenStripPure2
    (bne_spec_gen_within .x8 .x18 0x1fe8#13 src2 (t + signExtend12 0xfa0#12) (bI + 96))
    (fun hp hq => hne (pure_end2 hp hq))
  have e1 : bI + 96 + signExtend13 0x1fe8#13 = bI + 72 := by rv64_addr
  rw [e1] at b1'
  have i2 := ri_it 0x000#12 0x000#12 0x020#12 0xfe0#12 (bI + 72) (f0 + signExtend12 0x008#12) src2
    dst2 dst1 src1 (BitVec.ofNat 64 0)
  rw [hf01, li_32] at i2
  simp only [add_se0] at i2
  have j2 := jal_spec_within .x1 (bI + 88 + 4) 0x003860#21 (bI + 88) (by decide)
  rw [h_bM] at j2
  have m2 := memmove32 bM dst2 src2 (bI + 88 + 4) ((extractByte a0 0).zeroExtend 64)
    (dst1 + BitVec.ofNat 64 0) b0 b1 b2 b3 z0 z1 z2 z3
    hs2a hd2a hs2o hd2o hs2v hd2v hlt2
  rw [h_ra] at m2
  have a2' := ri_adv 0x008#12 (bI + 92) (f0 + signExtend12 0x008#12)
  have b2' := cpsBranchWithin_ntakenStripPure2
    (bne_spec_gen_within .x8 .x18 0x1fe8#13 (src2 + signExtend12 0xfe0#12)
      (t + signExtend12 0xfa0#12) (bI + 96))
    (fun hp hq => (pure_end2 hp hq) heq)
  have tl := ri_tail 0x008#12 0x000#12 (bI + 100) ctx g st dst2 src2 g0
  rw [h_gcell] at tl
  simp only [add_se0] at tl
  have j3 := jal_spec_within .x1 (bI + 88 + 4) 0x004828#21 (bI + 112) (by decide)
  have hp := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bI (bI) Image.f_return_impl.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hp)
  have i1 := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bI (bI + 72) Image.f_return_impl.prog _ 18 (by rfl) (by decide) (by decide) (by decide)) i1)
  have j1 := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bI Image.f_return_impl.prog 22 (bI + 88) (by decide) (by decide) (by rfl))) j1)
  have m1 := cpsTripleWithin_extend_code hcM m1
  have a1' := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bI (bI + 92) Image.f_return_impl.prog _ 23 (by rfl) (by decide) (by decide) (by decide)) a1')
  have b1' := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bI Image.f_return_impl.prog 24 (bI + 96) (by decide) (by decide) (by rfl))) b1')
  have i2 := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bI (bI + 72) Image.f_return_impl.prog _ 18 (by rfl) (by decide) (by decide) (by decide)) i2)
  have j2 := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bI Image.f_return_impl.prog 22 (bI + 88) (by decide) (by decide) (by rfl))) j2)
  have m2 := cpsTripleWithin_extend_code hcM m2
  have a2' := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bI (bI + 92) Image.f_return_impl.prog _ 23 (by rfl) (by decide) (by decide) (by decide)) a2')
  have b2' := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bI Image.f_return_impl.prog 24 (bI + 96) (by decide) (by decide) (by rfl))) b2')
  have tl := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bI (bI + 100) Image.f_return_impl.prog _ 25 (by rfl) (by decide) (by decide) (by decide)) tl)
  have j3 := cpsTripleWithin_extend_code hcI (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bI Image.f_return_impl.prog 28 (bI + 112) (by decide) (by decide) (by rfl))) j3)
  runBlock hp i1 j1 m1 a1' b1' i2 j2 m2 a2' b2' tl j3

/-! ## `return_` -/

theorem ret_pro (oF oS o32 : BitVec 12) (base sp ra top bottom ip slot : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .SUB .x15 .x13 .x12, .SD .x2 .x1 oS, .ADDI .x12 .x0 o32])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x15 ↦ᵣ ip) ** ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ slot))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) **
       (.x12 ↦ᵣ ((0 : Word) + signExtend12 o32)) ** (.x13 ↦ᵣ top) **
       (.x15 ↦ᵣ (top - bottom)) ** ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ ra)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ret_args (oZ : BitVec 12) (base ctx a1v v12 top gas : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .ADDI .x11 .x10 oZ, .ADDI .x12 .x13 oZ, .ADDI .x10 .x0 oZ, .ADDI .x13 .x14 oZ])
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ a1v) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 oZ)) **
       (.x11 ↦ᵣ (ctx + signExtend12 oZ)) ** (.x12 ↦ᵣ (top + signExtend12 oZ)) **
       (.x13 ↦ᵣ (gas + signExtend12 oZ)) ** (.x14 ↦ᵣ gas)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The RETURN handler with two operands present, up to its call of
    `return_impl(Success, ctx, top, gas)`. -/
theorem return_spec (base sp ra top bottom ip slot ctx a1v gas mslot : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (hdepth : BitVec.slt ((0 : Word) + signExtend12 0x020#12) (top - bottom)) :
    cpsTripleWithin 10 base (base + 36 + signExtend21 0x1fff68#21)
      (CodeReq.ofProg base Image.f_return.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ a1v) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) ** (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (mslot ↦ₘ slot))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (base + 36 + 4)) ** (.x2 ↦ᵣ (sp + signExtend12 0xff0#12)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 0x000#12)) ** (.x11 ↦ᵣ ctx) ** (.x12 ↦ᵣ top) **
       (.x13 ↦ᵣ gas) ** (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ (top - bottom)) ** (mslot ↦ₘ ra)) := by
  have h0 := ret_pro 0xff0#12 0x008#12 0x020#12 base sp ra top bottom ip slot
  rw [h_mslot] at h0
  have hb := cpsBranchWithin_ntakenStripPure2
    (bge_spec_gen_within .x12 .x15 0x0018#13 ((0 : Word) + signExtend12 0x020#12) (top - bottom) (base + 16))
    (fun hp hq => (pure_end2 hp hq) hdepth)
  have h1 := ret_args 0x000#12 (base + 20) ctx a1v ((0 : Word) + signExtend12 0x020#12) top gas
  rw [add_se0 ctx, add_se0 top, add_se0 gas] at h1
  have hj := jal_spec_within .x1 ra 0x1fff68#21 (base + 36) (by decide)
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_return.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hb := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_return.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hb
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 20) Image.f_return.prog _ 5 (by rfl) (by decide) (by decide) (by decide)) h1
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_return.prog 9 (base + 36) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hb h1 hj

end PureInterp.Handlers
