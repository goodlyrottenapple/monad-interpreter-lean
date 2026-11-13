import PureInterp.Entry.Alloc
import PureInterp.Entry.Memset
import PureInterp.Entry.Memcpy

/-!
# `Intercode::pad`, first part

Entry of `pad(code)` up to the size test after the first `memset`:
spill callee-saved registers, check `size < 2^20`, allocate `size + 63` bytes
with `operator new[]`, zero the first 30 bytes.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem pad_prologue (oF o1 o2 o3 o4 o5 o6 o7 : BitVec 12) (hi : BitVec 20)
    (base sp ra s0 s1 s2 s3 cp nW r15 m0 m1 m2 m3 m4 m5 m6 : Word) :
    cpsTripleWithin 9 base (base + 36) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .SD .x2 .x1 o1, .SD .x2 .x8 o2, .SD .x2 .x9 o3, .SD .x2 .x18 o4,
      .SD .x2 .x19 o5, .SD .x2 .x10 o6, .SD .x2 .x11 o7, .LUI .x15 hi])
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) **
       (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ cp) ** (.x11 ↦ᵣ nW) ** (.x15 ↦ᵣ r15) **
       ((sp + signExtend12 oF + signExtend12 o1) ↦ₘ m0) **
       ((sp + signExtend12 oF + signExtend12 o2) ↦ₘ m1) **
       ((sp + signExtend12 oF + signExtend12 o3) ↦ₘ m2) **
       ((sp + signExtend12 oF + signExtend12 o4) ↦ₘ m3) **
       ((sp + signExtend12 oF + signExtend12 o5) ↦ₘ m4) **
       ((sp + signExtend12 oF + signExtend12 o6) ↦ₘ m5) **
       ((sp + signExtend12 oF + signExtend12 o7) ↦ₘ m6))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ cp) ** (.x11 ↦ᵣ nW) **
       (.x15 ↦ᵣ ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) **
       ((sp + signExtend12 oF + signExtend12 o1) ↦ₘ ra) **
       ((sp + signExtend12 oF + signExtend12 o2) ↦ₘ s0) **
       ((sp + signExtend12 oF + signExtend12 o3) ↦ₘ s1) **
       ((sp + signExtend12 oF + signExtend12 o4) ↦ₘ s2) **
       ((sp + signExtend12 oF + signExtend12 o5) ↦ₘ s3) **
       ((sp + signExtend12 oF + signExtend12 o6) ↦ₘ cp) **
       ((sp + signExtend12 oF + signExtend12 o7) ↦ₘ nW)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem pad_args1 (oA oB oC : BitVec 12) (base cp nW s0 s3 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .ADDI .x19 .x10 oA, .ADDI .x10 .x11 oB, .ADDI .x8 .x11 oC])
      ((.x8 ↦ᵣ s0) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ cp) ** (.x11 ↦ᵣ nW))
      ((.x8 ↦ᵣ (nW + signExtend12 oC)) ** (.x19 ↦ᵣ (cp + signExtend12 oA)) **
       (.x10 ↦ᵣ (nW + signExtend12 oB)) ** (.x11 ↦ᵣ nW)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem pad_args2 (oA oB oC : BitVec 12) (base buf r11 r12 s1 s2 : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .ADDI .x12 .x0 oA, .ADDI .x11 .x0 oB, .ADDI .x9 .x10 oC, .ADD .x18 .x10 .x12])
      ((.x0 ↦ᵣ 0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ r11) **
       (.x12 ↦ᵣ r12))
      ((.x0 ↦ᵣ 0) ** (.x9 ↦ᵣ (buf + signExtend12 oC)) **
       (.x18 ↦ᵣ (buf + ((0 : Word) + signExtend12 oA))) ** (.x10 ↦ᵣ buf) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 oB)) ** (.x12 ↦ᵣ ((0 : Word) + signExtend12 oA))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem li15 (o : BitVec 12) (base r15 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x15 .x0 o])
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ r15))
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ ((0 : Word) + signExtend12 o))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ptr_zero (b : Word) : b + BitVec.ofNat 64 0 = b := BitVec.add_zero b

theorem lui_100 : (((0x00100#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
    = BitVec.ofNat 64 (2 ^ 20) := by decide

theorem ofNat_ult (a b : Nat) (h : a < b) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem size63_ne (n : Nat) (h : n < 2 ^ 20) :
    BitVec.ofNat 64 n + signExtend12 0x03f#12 ≠ 0 := by
  rw [show signExtend12 0x03f#12 = BitVec.ofNat 64 63 from by decide, ← BitVec.ofNat_add]
  intro h0
  have := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat] at this
  have : (n + 63) % 2 ^ 64 = 0 := this
  omega

/-- `pad` from its entry to the size test at `bp + 80`. `buf = round32 hn` is
    the fresh buffer; its `n + 63` bytes are owned by the caller as
    `bytesRegion buf bs0`. -/
theorem pad_front (cr : CodeReq) (bp bn bm sp ra s0 s1 s2 s3 sbase r12 r14 r15 : Word)
    (m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf : Word) (c38 c30 c28 c20 c18 c00 c08 : Word)
    (bs0 : List (BitVec 8)) (j0 n : Nat)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i)
    (hcn : ∀ a i, CodeReq.ofProg bn Image.f_new_80009fb4.prog a = some i → cr a = some i)
    (hcm : ∀ a i, CodeReq.ofProg bm Image.f_memset.prog a = some i → cr a = some i)
    (h_bn : bp + 52 + signExtend21 0x1fff30#21 = bn)
    (h_bm : bp + 72 + signExtend21 0x1ffcec#21 = bm)
    (h_r1 : (bp + 52 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 56)
    (h_r2 : (bp + 72 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 76)
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
    (halign : buf.toNat % 8 = 0) (hlen : bs0.length = n + 63)
    (hover : buf.toNat + (n + 63) < 2 ^ 64)
    (hvalid : ∀ i, i < n + 63 → isValidByteAccess (buf + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 128 bp (bp + 80) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) **
       (.x11 ↦ᵣ BitVec.ofNat 64 n) ** (.x12 ↦ᵣ r12) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (c38 ↦ₘ m0) ** (c30 ↦ₘ m1) ** (c28 ↦ₘ m2) ** (c20 ↦ₘ m3) ** (c18 ↦ₘ m4) **
       (c00 ↦ₘ m5) ** (c08 ↦ₘ m6) ** (hcell ↦ₘ hn) ** bytesRegion buf bs0)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bp + 72 + 4)) ** (.x2 ↦ᵣ (sp + signExtend12 0xfc0#12)) **
       (.x8 ↦ᵣ BitVec.ofNat 64 n) ** (.x9 ↦ᵣ buf) ** (.x18 ↦ᵣ (buf + BitVec.ofNat 64 30)) **
       (.x19 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ 0) **
       (.x12 ↦ᵣ BitVec.ofNat 64 30) ** (.x14 ↦ᵣ (buf + BitVec.ofNat 64 (0 + 30))) **
       (.x15 ↦ᵣ 1) **
       (c38 ↦ₘ ra) ** (c30 ↦ₘ s0) ** (c28 ↦ₘ s1) ** (c20 ↦ₘ s2) ** (c18 ↦ₘ s3) **
       (c00 ↦ₘ (sbase + BitVec.ofNat 64 j0)) ** (c08 ↦ₘ BitVec.ofNat 64 n) **
       (hcell ↦ₘ (BitVec.ofNat 64 n + signExtend12 0x03f#12 + buf)) **
       bytesRegion buf (splice bs0 0 (List.replicate 30 0))) := by
  have h0 := pad_prologue 0xfc0#12 0x038#12 0x030#12 0x028#12 0x020#12 0x018#12 0x000#12 0x008#12
    0x00100#20 bp sp ra s0 s1 s2 s3 (sbase + BitVec.ofNat 64 j0) (BitVec.ofNat 64 n) r15
    m0 m1 m2 m3 m4 m5 m6
  rw [h_c38, h_c30, h_c28, h_c20, h_c18, h_c00, h_c08, lui_100] at h0
  have hbgeu := cpsBranchWithin_ntakenStripPure2
    (bgeu_spec_gen_within .x11 .x15 0x0084#13 (BitVec.ofNat 64 n) (BitVec.ofNat 64 (2 ^ 20)) (bp + 36))
    (fun hp hq => (pure_end2 hp hq) (ofNat_ult n (2 ^ 20) hsize (by decide)))
  have h1 := pad_args1 0x000#12 0x03f#12 0x000#12 (bp + 40) (sbase + BitVec.ofNat 64 j0)
    (BitVec.ofNat 64 n) s0 s3
  simp only [add_se12_zero] at h1
  have hj1 := jal_spec_within .x1 ra 0x1fff30#21 (bp + 52) (by decide)
  rw [h_bn] at hj1
  have hnew := new_9fb4_spec bn (bp + 52 + 4) (BitVec.ofNat 64 n + signExtend12 0x03f#12) r14
    (BitVec.ofNat 64 (2 ^ 20)) hn hcell hend h_hcell1 h_hend h_hcell3 (size63_ne n hsize) hfit
  rw [h_r1, add_se12_zero, h_buf] at hnew
  have h2 := pad_args2 0x01e#12 0x000#12 0x000#12 (bp + 56) buf (BitVec.ofNat 64 n) r12 s1 s2
  rw [show (0 : Word) + signExtend12 0x01e#12 = BitVec.ofNat 64 30 from by decide] at h2
  simp only [add_se12_zero] at h2
  have hj2 := jal_spec_within .x1 (bp + 52 + 4) 0x1ffcec#21 (bp + 72) (by decide)
  rw [h_bm] at hj2
  have hm := memset_spec bm (bp + 72 + 4) buf 0
    (bn + (48 : Word) + (4 : Word) + (((0x1fff7#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)
    buf bs0 0 30 halign (by omega) (by omega) (fun i _ hi => hvalid i (by omega))
  rw [h_r2, ptr_zero, show ((0 : Word).truncate 8) = (0 : BitVec 8) from rfl] at hm
  have h3 := li15 0x001#12 (bp + 76) (buf + BitVec.ofNat 64 (0 + 30))
  rw [show (0 : Word) + signExtend12 0x001#12 = 1 from by decide] at h3
  have h0 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp bp Image.f_Intercode_pad.prog _ 0 (by simp) (by decide) (by decide) (by decide) a i h)) h0
  have hbgeu := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 9 (bp + 36) (by decide) (by decide) (by rfl)) a i h)) hbgeu
  have h1 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp (bp + 40) Image.f_Intercode_pad.prog _ 10 (by rfl) (by decide) (by decide) (by decide) a i h)) h1
  have hj1 := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 13 (bp + 52) (by decide) (by decide) (by rfl)) a i h)) hj1
  have hnew := cpsTripleWithin_extend_code hcn hnew
  have h2 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp (bp + 56) Image.f_Intercode_pad.prog _ 14 (by rfl) (by decide) (by decide) (by decide) a i h)) h2
  have hj2 := cpsTripleWithin_extend_code (fun a i h => hcp a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bp Image.f_Intercode_pad.prog 18 (bp + 72) (by decide) (by decide) (by rfl)) a i h)) hj2
  have hm := cpsTripleWithin_extend_code hcm hm
  have h3 := cpsTripleWithin_extend_code (fun a i h => hcp a i
    (CodeReq.ofProg_mono_sub bp (bp + 76) Image.f_Intercode_pad.prog _ 19 (by rfl) (by decide) (by decide) (by decide) a i h)) h3
  runBlock h0 hbgeu h1 hj1 hnew h2 hj2 hm h3

end PureInterp.Entry
