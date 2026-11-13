import PureInterp.Entry.PadFront
import PureInterp.Entry.PadLists

/-!
# `Intercode::pad`

`pad(code)` allocates `size + 63` bytes, zero-fills the first 30, copies the
code after them, zero-fills the last 33 and returns `buffer + 30`.
(`start_padding_size = 30`, `end_padding_size = 33` in `intercode.hpp`.)

GCC compiles `std::copy` into three cases: `memcpy` for `size ≥ 2`, one
`lbu`/`sb` pair for `size = 1`, nothing for `size = 0`. `pad_spec` covers all
three with one statement: the buffer holds
`replicate 30 0 ++ code ++ replicate 33 0`.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem pad_args3 (oA oB oC : BitVec 12) (base cp nW b30 r10 r11 r12 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .ADDI .x11 .x19 oA, .ADDI .x12 .x8 oB, .ADDI .x10 .x18 oC])
      ((.x8 ↦ᵣ nW) ** (.x18 ↦ᵣ b30) ** (.x19 ↦ᵣ cp) ** (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) **
       (.x12 ↦ᵣ r12))
      ((.x8 ↦ᵣ nW) ** (.x18 ↦ᵣ b30) ** (.x19 ↦ᵣ cp) ** (.x10 ↦ᵣ (b30 + signExtend12 oC)) **
       (.x11 ↦ᵣ (cp + signExtend12 oA)) ** (.x12 ↦ᵣ (nW + signExtend12 oB))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem pad_args4 (oA oB oC : BitVec 12) (base nW buf r10 r11 r12 : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .ADDI .x10 .x8 oA, .ADD .x10 .x9 .x10, .ADDI .x12 .x0 oB, .ADDI .x11 .x0 oC])
      ((.x0 ↦ᵣ 0) ** (.x8 ↦ᵣ nW) ** (.x9 ↦ᵣ buf) ** (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) **
       (.x12 ↦ᵣ r12))
      ((.x0 ↦ᵣ 0) ** (.x8 ↦ᵣ nW) ** (.x9 ↦ᵣ buf) ** (.x10 ↦ᵣ (buf + (nW + signExtend12 oA))) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 oC)) ** (.x12 ↦ᵣ ((0 : Word) + signExtend12 oB))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem pad_epilogue (o1 o2 o3 o4 o5 oZ oF : BitVec 12)
    (base spf r1 r8 r9 r19 b30 r10 v1 v2 v3 v4 v5 : Word) :
    cpsTripleWithin 7 base (base + 28) (CodeReq.ofProg base [
      .LD .x1 .x2 o1, .LD .x8 .x2 o2, .LD .x9 .x2 o3, .LD .x19 .x2 o5, .ADDI .x10 .x18 oZ,
      .LD .x18 .x2 o4, .ADDI .x2 .x2 oF])
      ((.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ spf) ** (.x8 ↦ᵣ r8) ** (.x9 ↦ᵣ r9) ** (.x18 ↦ᵣ b30) **
       (.x19 ↦ᵣ r19) ** (.x10 ↦ᵣ r10) **
       ((spf + signExtend12 o1) ↦ₘ v1) ** ((spf + signExtend12 o2) ↦ₘ v2) **
       ((spf + signExtend12 o3) ↦ₘ v3) ** ((spf + signExtend12 o4) ↦ₘ v4) **
       ((spf + signExtend12 o5) ↦ₘ v5))
      ((.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ (spf + signExtend12 oF)) ** (.x8 ↦ᵣ v2) ** (.x9 ↦ᵣ v3) **
       (.x18 ↦ᵣ v4) ** (.x19 ↦ᵣ v5) ** (.x10 ↦ᵣ (b30 + signExtend12 oZ)) **
       ((spf + signExtend12 o1) ↦ₘ v1) ** ((spf + signExtend12 o2) ↦ₘ v2) **
       ((spf + signExtend12 o3) ↦ₘ v3) ** ((spf + signExtend12 o4) ↦ₘ v4) **
       ((spf + signExtend12 o5) ↦ₘ v5)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem tail_ptr (buf : Word) (n : Nat) :
    buf + (BitVec.ofNat 64 n + signExtend12 0x01e#12) = buf + BitVec.ofNat 64 (30 + n) := by
  rw [show signExtend12 0x01e#12 = BitVec.ofNat 64 30 from by decide, ← BitVec.ofNat_add,
    Nat.add_comm]

theorem pad_frame (sp : Word) : sp + signExtend12 0xfc0#12 + signExtend12 0x040#12 = sp := by
  rw [BitVec.add_assoc, show signExtend12 0xfc0#12 + signExtend12 0x040#12 = (0 : Word) from by decide]
  exact BitVec.add_zero sp

theorem one_slt (n : Nat) (h2 : 2 ≤ n) (h : n < 2 ^ 20) :
    BitVec.slt (1 : Word) (BitVec.ofNat 64 n) = true := by
  rw [BitVec.slt_iff_toInt_lt]
  simp [BitVec.toInt_eq_toNat_cond]
  omega

/-- `pad` from `bp + 100` (after the copy) to its return: zero the last 33
    bytes, restore the callee-saved registers, return `buf + 30`. -/
theorem pad_tail (cr : CodeReq) (bp bm sp ra s0 s1 s2 s3 buf r1 r10 r11 r12 r14 r15 r19 : Word)
    (c38 c30 c28 c20 c18 : Word) (bs2 : List (BitVec 8)) (n : Nat)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i)
    (hcm : ∀ a i, CodeReq.ofProg bm Image.f_memset.prog a = some i → cr a = some i)
    (h_bm : bp + 116 + signExtend21 0x1ffcc0#21 = bm)
    (h_r4 : (bp + 116 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 120)
    (h_c38 : sp + signExtend12 0xfc0#12 + signExtend12 0x038#12 = c38)
    (h_c30 : sp + signExtend12 0xfc0#12 + signExtend12 0x030#12 = c30)
    (h_c28 : sp + signExtend12 0xfc0#12 + signExtend12 0x028#12 = c28)
    (h_c20 : sp + signExtend12 0xfc0#12 + signExtend12 0x020#12 = c20)
    (h_c18 : sp + signExtend12 0xfc0#12 + signExtend12 0x018#12 = c18)
    (halign : buf.toNat % 8 = 0) (hlen : bs2.length = n + 63)
    (hover : buf.toNat + (n + 63) < 2 ^ 64)
    (hvalid : ∀ i, i < n + 63 → isValidByteAccess (buf + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 116 (bp + 100) ((ra + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ (sp + signExtend12 0xfc0#12)) **
       (.x8 ↦ᵣ BitVec.ofNat 64 n) ** (.x9 ↦ᵣ buf) ** (.x18 ↦ᵣ (buf + BitVec.ofNat 64 30)) **
       (.x19 ↦ᵣ r19) ** (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x12 ↦ᵣ r12) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) **
       (c38 ↦ₘ ra) ** (c30 ↦ₘ s0) ** (c28 ↦ₘ s1) ** (c20 ↦ₘ s2) ** (c18 ↦ₘ s3) **
       bytesRegion buf bs2)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ (buf + BitVec.ofNat 64 30)) ** (.x11 ↦ᵣ 0) **
       (.x12 ↦ᵣ BitVec.ofNat 64 33) ** (.x14 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n + 33))) **
       (.x15 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n + 33))) **
       (c38 ↦ₘ ra) ** (c30 ↦ₘ s0) ** (c28 ↦ₘ s1) ** (c20 ↦ₘ s2) ** (c18 ↦ₘ s3) **
       bytesRegion buf (splice bs2 (30 + n) (List.replicate 33 0))) := by
  have h4 := pad_args4 0x01e#12 0x021#12 0x000#12 (bp + 100) (BitVec.ofNat 64 n) buf r10 r11 r12
  rw [tail_ptr, show (0 : Word) + signExtend12 0x021#12 = BitVec.ofNat 64 33 from by decide] at h4
  simp only [add_se12_zero] at h4
  have hj := jal_spec_within .x1 r1 0x1ffcc0#21 (bp + 116) (by decide)
  rw [h_bm] at hj
  have hm := memset_spec bm (bp + 116 + 4) buf 0 r14 r15 bs2 (30 + n) 33 halign (by omega)
    (by omega) (fun i _ hi => hvalid i (by omega))
  rw [h_r4, show ((0 : Word).truncate 8) = (0 : BitVec 8) from rfl] at hm
  have h5 := pad_epilogue 0x038#12 0x030#12 0x028#12 0x020#12 0x018#12 0x000#12 0x040#12
    (bp + 120) (sp + signExtend12 0xfc0#12) (bp + 116 + 4) (BitVec.ofNat 64 n) buf r19
    (buf + BitVec.ofNat 64 30) (buf + BitVec.ofNat 64 (30 + n)) ra s0 s1 s2 s3
  rw [h_c38, h_c30, h_c28, h_c20, h_c18, pad_frame, add_se12_zero] at h5
  have hr := jalr_x0_spec_gen_within .x1 ra 0x000#12 (bp + 148)
  have h4 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp (bp + 100) Image.f_Intercode_pad.prog _ 25 (by rfl) (by decide) (by decide) (by decide) a i h)) h4
  have hj := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 29 (bp + 116) (by decide) (by decide) (by rfl)) a i h)) hj
  have hm := cpsTripleWithin_extend_code hcm hm
  have h5 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp (bp + 120) Image.f_Intercode_pad.prog _ 30 (by rfl) (by decide) (by decide) (by decide) a i h)) h5
  have hr := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 37 (bp + 148) (by decide) (by decide) (by rfl)) a i h)) hr
  runBlock h4 hj hm h5 hr

/-- The copy for `size ≥ 2`: `memcpy(buf + 30, code, size)`. -/
theorem pad_mid_copy (cr : CodeReq) (bp bc sbase buf r1 r10 r11 r12 r14 : Word)
    (sbs bs1 : List (BitVec 8)) (j0 n : Nat)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i)
    (hcc : ∀ a i, CodeReq.ofProg bc Image.f_memcpy.prog a = some i → cr a = some i)
    (h_bc : bp + 96 + signExtend21 0x1ffc60#21 = bc)
    (h_r3 : (bp + 96 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 100)
    (h2 : 2 ≤ n) (hsize : n < 2 ^ 20)
    (salign : sbase.toNat % 8 = 0) (slen : j0 + n ≤ sbs.length)
    (sover : sbase.toNat + (j0 + n) < 2 ^ 64)
    (svalid : ∀ j, j0 ≤ j → j < j0 + n → isValidByteAccess (sbase + BitVec.ofNat 64 j) = true)
    (halign : buf.toNat % 8 = 0) (hlen : bs1.length = n + 63)
    (hover : buf.toNat + (n + 63) < 2 ^ 64)
    (hvalid : ∀ i, i < n + 63 → isValidByteAccess (buf + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (5 * n + 9) (bp + 80) (bp + 100) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x8 ↦ᵣ BitVec.ofNat 64 n) **
       (.x18 ↦ᵣ (buf + BitVec.ofNat 64 30)) ** (.x19 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) **
       (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x12 ↦ᵣ r12) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ 1) **
       bytesRegion sbase sbs ** bytesRegion buf bs1)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bp + 96 + 4)) ** (.x8 ↦ᵣ BitVec.ofNat 64 n) **
       (.x18 ↦ᵣ (buf + BitVec.ofNat 64 30)) ** (.x19 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) **
       (.x10 ↦ᵣ (buf + BitVec.ofNat 64 30)) **
       (.x11 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) **
       (.x12 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) **
       (.x14 ↦ᵣ ((sbs.getD (j0 + n - 1) 0).zeroExtend 64)) **
       (.x15 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n))) **
       bytesRegion sbase sbs ** bytesRegion buf (splice bs1 30 ((sbs.drop j0).take n))) := by
  have hbge := cpsBranchWithin_ntakenStripPure2
    (bge_spec_gen_within .x15 .x8 0x0048#13 1 (BitVec.ofNat 64 n) (bp + 80))
    (fun hp hq => (pure_end2 hp hq) (one_slt n h2 hsize))
  have h3 := pad_args3 0x000#12 0x000#12 0x000#12 (bp + 84) (sbase + BitVec.ofNat 64 j0)
    (BitVec.ofNat 64 n) (buf + BitVec.ofNat 64 30) r10 r11 r12
  simp only [add_se12_zero] at h3
  have hj := jal_spec_within .x1 r1 0x1ffc60#21 (bp + 96) (by decide)
  rw [h_bc] at hj
  have hc := memcpy_spec bc (bp + 96 + 4) sbase buf r14 1 sbs bs1 j0 30 n (by omega)
    salign slen sover svalid halign (by omega) (by omega) (fun i _ hi => hvalid i (by omega))
  rw [h_r3] at hc
  have hbge := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 20 (bp + 80) (by decide) (by decide) (by rfl)) a i h)) hbge
  have h3 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp (bp + 84) Image.f_Intercode_pad.prog _ 21 (by rfl) (by decide) (by decide) (by decide) a i h)) h3
  have hj := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 24 (bp + 96) (by decide) (by decide) (by rfl)) a i h)) hj
  have hc := cpsTripleWithin_extend_code hcc hc
  runBlock hbge h3 hj hc

/-- The copy for `size = 1`: one `lbu`/`sb` pair. -/
theorem pad_mid_one (cr : CodeReq) (bp sbase buf : Word)
    (sbs bs1 : List (BitVec 8)) (j0 : Nat)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i)
    (salign : sbase.toNat % 8 = 0) (slen : j0 < sbs.length)
    (sover : sbase.toNat + j0 < 2 ^ 64)
    (svalid : isValidByteAccess (sbase + BitVec.ofNat 64 j0) = true)
    (halign : buf.toNat % 8 = 0) (hlen : 30 < bs1.length)
    (hover : buf.toNat + 30 < 2 ^ 64)
    (hvalid : isValidByteAccess (buf + BitVec.ofNat 64 30) = true) :
    cpsTripleWithin 5 (bp + 80) (bp + 100) cr
      ((.x8 ↦ᵣ BitVec.ofNat 64 1) ** (.x9 ↦ᵣ buf) **
       (.x19 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) ** (.x15 ↦ᵣ 1) **
       bytesRegion sbase sbs ** bytesRegion buf bs1)
      ((.x8 ↦ᵣ BitVec.ofNat 64 1) ** (.x9 ↦ᵣ buf) **
       (.x19 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) **
       (.x15 ↦ᵣ ((sbs.getD j0 0).zeroExtend 64)) **
       bytesRegion sbase sbs ** bytesRegion buf (bs1.set 30 (sbs.getD j0 0))) := by
  have hbge := cpsBranchWithin_takenStripPure2
    (bge_spec_gen_within .x15 .x8 0x0048#13 1 (BitVec.ofNat 64 1) (bp + 80))
    (fun hp hq => absurd (pure_end2 hp hq) (by decide))
  have e : bp + 80 + signExtend13 0x0048#13 = bp + 152 := by rv64_addr
  rw [e] at hbge
  have hbne := cpsBranchWithin_ntakenStripPure2
    (bne_spec_gen_within .x8 .x15 0x1fcc#13 (BitVec.ofNat 64 1) 1 (bp + 152))
    (fun hp hq => (pure_end2 hp hq) rfl)
  have hl := lbu_region_at .x15 .x19 sbase (sbase + BitVec.ofNat 64 j0) 1 0x000#12
    (bp + 156) sbs j0 (by decide) (add_se12_zero _) salign slen sover svalid
  rw [← getD_of_lt sbs j0 slen] at hl
  have hs := sb_region_at .x9 .x15 buf buf ((sbs.getD j0 0).zeroExtend 64) 0x01e#12
    (bp + 160) bs1 30
    (by rw [show signExtend12 0x01e#12 = BitVec.ofNat 64 30 from by decide])
    halign hlen hover hvalid
  rw [trunc_zext] at hs
  have hj := jal_x0_spec_gen_within 0x1fffc0#21 (bp + 164)
  have e2 : bp + 164 + signExtend21 0x1fffc0#21 = bp + 100 := by rv64_addr
  rw [e2] at hj
  have hbge := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 20 (bp + 80) (by decide) (by decide) (by rfl)) a i h)) hbge
  have hbne := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 38 (bp + 152) (by decide) (by decide) (by rfl)) a i h)) hbne
  have hl := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 39 (bp + 156) (by decide) (by decide) (by rfl)) a i h)) hl
  have hs := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 40 (bp + 160) (by decide) (by decide) (by rfl)) a i h)) hs
  have hj := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 41 (bp + 164) (by decide) (by decide) (by rfl)) a i h)) hj
  runBlock hbge hbne hl hs hj

/-- No copy for `size = 0`. -/
theorem pad_mid_zero (cr : CodeReq) (bp : Word)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i) :
    cpsTripleWithin 2 (bp + 80) (bp + 100) cr
      ((.x8 ↦ᵣ BitVec.ofNat 64 0) ** (.x15 ↦ᵣ 1))
      ((.x8 ↦ᵣ BitVec.ofNat 64 0) ** (.x15 ↦ᵣ 1)) := by
  have hbge := cpsBranchWithin_takenStripPure2
    (bge_spec_gen_within .x15 .x8 0x0048#13 1 (BitVec.ofNat 64 0) (bp + 80))
    (fun hp hq => absurd (pure_end2 hp hq) (by decide))
  have e : bp + 80 + signExtend13 0x0048#13 = bp + 152 := by rv64_addr
  rw [e] at hbge
  have hbne := cpsBranchWithin_takenStripPure2
    (bne_spec_gen_within .x8 .x15 0x1fcc#13 (BitVec.ofNat 64 0) 1 (bp + 152))
    (fun hp hq => absurd (pure_end2 hp hq) (by decide))
  have e2 : bp + 152 + signExtend13 0x1fcc#13 = bp + 100 := by rv64_addr
  rw [e2] at hbne
  have hbge := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 20 (bp + 80) (by decide) (by decide) (by rfl)) a i h)) hbge
  have hbne := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 38 (bp + 152) (by decide) (by decide) (by rfl)) a i h)) hbne
  runBlock hbge hbne


/-- **`Intercode::pad(code)`**, all sizes below `2^20`. The code is the range
    `[j0, j0 + n)` of the caller's region `sbs`; `buf = round32 hn` is the
    fresh allocation, whose `n + 63` bytes the caller owns as `bs0`. On return
    `a0 = buf + 30` and the buffer holds 30 zero bytes, the code, 33 zero
    bytes; callee-saved registers and `sp` are restored and the heap pointer
    is advanced by `n + 63`. -/
theorem pad_spec (cr : CodeReq) (bp bn bm bc sp ra s0 s1 s2 s3 sbase r12 r14 r15 : Word)
    (m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf : Word) (c38 c30 c28 c20 c18 c00 c08 : Word)
    (sbs bs0 : List (BitVec 8)) (j0 n : Nat)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i)
    (hcn : ∀ a i, CodeReq.ofProg bn Image.f_new_80009fb4.prog a = some i → cr a = some i)
    (hcm : ∀ a i, CodeReq.ofProg bm Image.f_memset.prog a = some i → cr a = some i)
    (hcc : ∀ a i, CodeReq.ofProg bc Image.f_memcpy.prog a = some i → cr a = some i)
    (h_bn : bp + 52 + signExtend21 0x1fff30#21 = bn)
    (h_bm : bp + 72 + signExtend21 0x1ffcec#21 = bm)
    (h_bc : bp + 96 + signExtend21 0x1ffc60#21 = bc)
    (h_bm2 : bp + 116 + signExtend21 0x1ffcc0#21 = bm)
    (h_r1 : (bp + 52 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 56)
    (h_r2 : (bp + 72 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 76)
    (h_r3 : (bp + 96 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 100)
    (h_r4 : (bp + 116 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 120)
    (h_c38 : sp + signExtend12 0xfc0#12 + signExtend12 0x038#12 = c38)
    (h_c30 : sp + signExtend12 0xfc0#12 + signExtend12 0x030#12 = c30)
    (h_c28 : sp + signExtend12 0xfc0#12 + signExtend12 0x028#12 = c28)
    (h_c20 : sp + signExtend12 0xfc0#12 + signExtend12 0x020#12 = c20)
    (h_c18 : sp + signExtend12 0xfc0#12 + signExtend12 0x018#12 = c18)
    (h_c00 : sp + signExtend12 0xfc0#12 + signExtend12 0x000#12 = c00)
    (h_c08 : sp + signExtend12 0xfc0#12 + signExtend12 0x008#12 = c08)
    (h_hcell1 : pcrel (bn + 4) 0x1fff7#20 0x9a8#12 = hcell)
    (h_hend : pcrel (bn + 12) 0x23ff7#20 0x9c0#12 = hend)
    (h_hcell3 : pcrel (bn + 48 + 4) 0x1fff7#20 0x978#12 = hcell)
    (h_buf : round32 hn = buf)
    (hsize : n < 2 ^ 20)
    (hfit : ¬ BitVec.ult (hend - round32 hn) (BitVec.ofNat 64 n + signExtend12 0x03f#12))
    (salign : sbase.toNat % 8 = 0) (slen : j0 + n ≤ sbs.length)
    (sover : sbase.toNat + (j0 + n) < 2 ^ 64)
    (svalid : ∀ j, j0 ≤ j → j < j0 + n → isValidByteAccess (sbase + BitVec.ofNat 64 j) = true)
    (halign : buf.toNat % 8 = 0) (hlen : bs0.length = n + 63)
    (hover : buf.toNat + (n + 63) < 2 ^ 64)
    (hvalid : ∀ i, i < n + 63 → isValidByteAccess (buf + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (5 * n + 253) bp ((ra + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) **
       (.x11 ↦ᵣ BitVec.ofNat 64 n) ** (.x12 ↦ᵣ r12) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (c38 ↦ₘ m0) ** (c30 ↦ₘ m1) ** (c28 ↦ₘ m2) ** (c20 ↦ₘ m3) ** (c18 ↦ₘ m4) **
       (c00 ↦ₘ m5) ** (c08 ↦ₘ m6) ** (hcell ↦ₘ hn) ** bytesRegion sbase sbs **
       bytesRegion buf bs0)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ (buf + BitVec.ofNat 64 30)) ** (.x11 ↦ᵣ 0) **
       (.x12 ↦ᵣ BitVec.ofNat 64 33) ** (.x14 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n + 33))) **
       (.x15 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n + 33))) **
       (c38 ↦ₘ ra) ** (c30 ↦ₘ s0) ** (c28 ↦ₘ s1) ** (c20 ↦ₘ s2) ** (c18 ↦ₘ s3) **
       (c00 ↦ₘ (sbase + BitVec.ofNat 64 j0)) ** (c08 ↦ₘ BitVec.ofNat 64 n) **
       (hcell ↦ₘ (BitVec.ofNat 64 n + signExtend12 0x03f#12 + buf)) ** bytesRegion sbase sbs **
       bytesRegion buf
         (List.replicate 30 0 ++ (sbs.drop j0).take n ++ List.replicate 33 0)) := by
  have hl1 : (splice bs0 0 (List.replicate 30 0)).length = n + 63 := by
    rw [splice_length _ _ _ (by simp; omega)]; exact hlen
  by_cases h0 : n = 0
  · subst h0
    have hf := pad_front cr bp bn bm sp ra s0 s1 s2 s3 sbase r12 r14 r15 m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf c38 c30 c28 c20 c18 c00 c08 bs0 j0 0 hcp hcn hcm h_bn h_bm h_r1 h_r2 h_c38 h_c30 h_c28 h_c20 h_c18 h_c00 h_c08 h_hcell1 h_hend h_hcell3 h_buf hsize hfit halign hlen hover hvalid
    have hm := pad_mid_zero cr bp hcp
    have ht := pad_tail cr bp bm sp ra s0 s1 s2 s3 buf (bp + 72 + 4) buf 0 (BitVec.ofNat 64 30) (buf + BitVec.ofNat 64 (0 + 30)) 1 (sbase + BitVec.ofNat 64 j0) c38 c30 c28 c20 c18 (splice bs0 0 (List.replicate 30 0)) 0 hcp hcm h_bm2 h_r4 h_c38 h_c30 h_c28 h_c20 h_c18 halign hl1 hover hvalid
    have e := pad_bytes bs0 [] 0 hlen rfl
    rw [splice_nil] at e
    rw [e] at ht
    simp only [List.take_zero]
    (runBlock hf hm ht)
  by_cases h1 : n = 1
  · subst h1
    have hj : j0 < sbs.length := by omega
    have hf := pad_front cr bp bn bm sp ra s0 s1 s2 s3 sbase r12 r14 r15 m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf c38 c30 c28 c20 c18 c00 c08 bs0 j0 1 hcp hcn hcm h_bn h_bm h_r1 h_r2 h_c38 h_c30 h_c28 h_c20 h_c18 h_c00 h_c08 h_hcell1 h_hend h_hcell3 h_buf hsize hfit halign hlen hover hvalid
    have hm := pad_mid_one cr bp sbase buf sbs (splice bs0 0 (List.replicate 30 0)) j0 hcp salign hj (by omega)
      (svalid j0 (by omega) (by omega)) halign (by omega) (by omega) (hvalid 30 (by omega))
    have ht := pad_tail cr bp bm sp ra s0 s1 s2 s3 buf (bp + 72 + 4) buf 0 (BitVec.ofNat 64 30) (buf + BitVec.ofNat 64 (0 + 30)) ((sbs.getD j0 0).zeroExtend 64) (sbase + BitVec.ofNat 64 j0) c38 c30 c28 c20 c18 ((splice bs0 0 (List.replicate 30 0)).set 30 (sbs.getD j0 0)) 1 hcp hcm h_bm2 h_r4 h_c38 h_c30 h_c28 h_c20 h_c18 halign (by rw [List.length_set]; exact hl1) hover hvalid
    have e := pad_bytes bs0 [sbs.getD j0 0] 1 hlen rfl
    rw [← set_eq_splice_one _ 30 _ (by omega)] at e
    rw [e] at ht
    rw [take_one_drop sbs j0 hj]
    (runBlock hf hm ht)
  · have h2 : 2 ≤ n := by omega
    have hf := pad_front cr bp bn bm sp ra s0 s1 s2 s3 sbase r12 r14 r15 m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf c38 c30 c28 c20 c18 c00 c08 bs0 j0 n hcp hcn hcm h_bn h_bm h_r1 h_r2 h_c38 h_c30 h_c28 h_c20 h_c18 h_c00 h_c08 h_hcell1 h_hend h_hcell3 h_buf hsize hfit halign hlen hover hvalid
    have hm := pad_mid_copy cr bp bc sbase buf (bp + 72 + 4) buf 0 (BitVec.ofNat 64 30)
      (buf + BitVec.ofNat 64 (0 + 30)) sbs (splice bs0 0 (List.replicate 30 0)) j0 n hcp hcc h_bc h_r3 h2 hsize
      salign slen sover svalid halign hl1 hover hvalid
    have ht := pad_tail cr bp bm sp ra s0 s1 s2 s3 buf (bp + 96 + 4) (buf + BitVec.ofNat 64 30) (sbase + BitVec.ofNat 64 (j0 + n)) (sbase + BitVec.ofNat 64 (j0 + n)) ((sbs.getD (j0 + n - 1) 0).zeroExtend 64) (buf + BitVec.ofNat 64 (30 + n)) (sbase + BitVec.ofNat 64 j0) c38 c30 c28 c20 c18 (splice (splice bs0 0 (List.replicate 30 0)) 30 ((sbs.drop j0).take n)) n hcp hcm h_bm2 h_r4 h_c38 h_c30 h_c28 h_c20 h_c18 halign (by rw [splice_length _ _ _ (by rw [List.length_take, List.length_drop, hl1]; omega)]; exact hl1) hover hvalid
    have e := pad_bytes bs0 ((sbs.drop j0).take n) n hlen (by simp; omega)
    rw [e] at ht
    (runBlock hf hm ht)

end PureInterp.Entry
