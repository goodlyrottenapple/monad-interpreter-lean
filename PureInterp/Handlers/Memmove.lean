import RiscvZkvm.Rv64.Logic
import PureInterp.Image.Index
import PureInterp.Handlers.Add
import PureInterp.Machine.Words

/-!
# `memmove`, copying backwards

`memmove` from `cxx/platform.cpp` is two byte loops. When the destination lies
above the source it copies from the last byte down; that is the direction
RETURN's copies of the offset and size words into the runtime context take
(the context is on the machine stack, above the operand stack). This file
proves that path for any non-zero length, over byte regions.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64 PureInterp.Machine

/-! ## Lists -/

theorem take_set_drop (S D : List (BitVec 8)) (j : Nat) (hs : j < S.length) (hd : j < D.length) :
    S.take j ++ (D.set j S[j]).drop j = S.take (j + 1) ++ D.drop (j + 1) := by
  rw [List.take_succ_eq_append_getElem hs, List.append_assoc]
  congr 1
  rw [List.set_eq_take_append_cons_drop, if_pos hd]
  rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]
  have : (List.take j D).length = j := by rw [List.length_take]; omega
  rw [List.drop_of_length_le (by omega)]
  rfl

theorem trunc_zext (b : BitVec 8) : ((b.zeroExtend 64 : Word).truncate 8) = b := by
  show (b.setWidth 64).setWidth 8 = b
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem dec_ofNat (j : Nat) :
    BitVec.ofNat 64 (j + 1) + signExtend12 0xfff#12 = BitVec.ofNat 64 j := by
  have h : (BitVec.ofNat 64 1 : Word) + signExtend12 0xfff#12 = 0 := by decide
  rw [BitVec.ofNat_add, BitVec.add_assoc, h]
  exact BitVec.add_zero _

set_option maxRecDepth 100000

/-! ## Blocks -/

theorem mm_dec (o : BitVec 12) (base c s v15 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .ADDI .x12 .x12 o, .ADD .x15 .x11 .x12])
      ((.x12 ↦ᵣ c) ** (.x11 ↦ᵣ s) ** (.x15 ↦ᵣ v15))
      ((.x12 ↦ᵣ (c + signExtend12 o)) ** (.x11 ↦ᵣ s) ** (.x15 ↦ᵣ (s + (c + signExtend12 o)))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem mm_dst (base c d v15 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADD .x15 .x10 .x12])
      ((.x12 ↦ᵣ c) ** (.x10 ↦ᵣ d) ** (.x15 ↦ᵣ v15))
      ((.x12 ↦ᵣ c) ** (.x10 ↦ᵣ d) ** (.x15 ↦ᵣ (d + c))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem mm_head (o1 o2 : BitVec 12) (base d s v14 v15 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .ADDI .x14 .x10 o1, .ADDI .x15 .x11 o2])
      ((.x10 ↦ᵣ d) ** (.x11 ↦ᵣ s) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15))
      ((.x10 ↦ᵣ d) ** (.x11 ↦ᵣ s) ** (.x14 ↦ᵣ (d + signExtend12 o1)) **
       (.x15 ↦ᵣ (s + signExtend12 o2))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-! ## One iteration -/

section
variable (base dst src : Word) (S : List (BitVec 8))
  (hsal : src.toNat % 8 = 0) (hdal : dst.toNat % 8 = 0)
  (hso : src.toNat + S.length ≤ 2 ^ 64)
  (hsv : ∀ i, i < S.length → isValidByteAccess (src + BitVec.ofNat 64 i) = true)

include hsal hdal hso hsv in
/-- Copy byte `j`: the loop body up to its closing branch. -/
theorem mm_iter (D : List (BitVec 8)) (j : Nat) (v14 v15 : Word)
    (hjs : j < S.length) (hjd : j < D.length)
    (hdo : dst.toNat + D.length ≤ 2 ^ 64)
    (hdv : ∀ i, i < D.length → isValidByteAccess (dst + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 5 (base + 16) (base + 36) (CodeReq.ofProg base Image.f_memmove.prog)
      ((.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) ** (.x12 ↦ᵣ BitVec.ofNat 64 (j + 1)) ** (.x14 ↦ᵣ v14) **
       (.x15 ↦ᵣ v15) ** bytesRegion src S ** bytesRegion dst D)
      ((.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) ** (.x12 ↦ᵣ BitVec.ofNat 64 j) **
       (.x14 ↦ᵣ ((S[j]).zeroExtend 64)) ** (.x15 ↦ᵣ (dst + BitVec.ofNat 64 j)) **
       bytesRegion src S ** bytesRegion dst (D.set j S[j])) := by
  have hA := mm_dec 0xfff#12 (base + 16) (BitVec.ofNat 64 (j + 1)) src v15
  rw [dec_ofNat] at hA
  have hL := bytesRegion_lbu_within .x14 .x15 src v14 (base + 24) S j (by decide) hsal hjs
    (by omega) (hsv j hjs)
  have hB := mm_dst (base + 28) (BitVec.ofNat 64 j) dst (src + BitVec.ofNat 64 j)
  have hS := bytesRegion_sb_within .x15 .x14 dst ((S[j]).zeroExtend 64) (base + 32) D j hdal hjd
    (by omega) (hdv j hjd)
  rw [trunc_zext] at hS
  have hA := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_memmove.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hA
  have hL := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hL
  have hB := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 28) Image.f_memmove.prog _ 7 (by rfl) (by decide) (by decide) (by decide)) hB
  have hS := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 8 (base + 32) (by decide) (by decide) (by rfl))) hS
  runBlock hA hL hB hS

theorem ofNat_ne_zero (k : Nat) (h : k + 1 < 2 ^ 64) : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt h] at this
  exact absurd this (by simp)

include hsal hdal hso hsv in
/-- The backward loop from its head with `k + 1` bytes left to its exit. -/
theorem mm_loop (hpos : 0 < S.length) : ∀ (k : Nat) (D : List (BitVec 8)) (v14 v15 : Word),
    k < S.length → k < D.length → k < 2 ^ 64 → dst.toNat + D.length ≤ 2 ^ 64 →
    (∀ i, i < D.length → isValidByteAccess (dst + BitVec.ofNat 64 i) = true) →
    cpsTripleWithin (6 * (k + 1)) (base + 16) (base + 40) (CodeReq.ofProg base Image.f_memmove.prog)
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) ** (.x12 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** bytesRegion src S ** bytesRegion dst D)
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) ** (.x12 ↦ᵣ BitVec.ofNat 64 0) **
       (.x14 ↦ᵣ ((S[0]'hpos).zeroExtend 64)) ** (.x15 ↦ᵣ (dst + BitVec.ofNat 64 0)) **
       bytesRegion src S ** bytesRegion dst (S.take (k + 1) ++ D.drop (k + 1))) := by
  intro k
  induction k with
  | zero =>
    intro D v14 v15 hks hkd _ hdo hdv
    have T := mm_iter base dst src S hsal hdal hso hsv D 0 v14 v15 hks hkd hdo hdv
    have e : D.set 0 S[0] = S.take (0 + 1) ++ D.drop (0 + 1) := by
      simpa using take_set_drop S D 0 hks hkd
    rw [e] at T
    have hbr := cpsBranchWithin_ntakenStripPure2
      (bne_spec_gen_within .x12 .x0 0x1fec#13 (BitVec.ofNat 64 0) 0 (base + 36))
      (fun hp hq => (pure_end2 hp hq) rfl)
    have hbr := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 9 (base + 36) (by decide) (by decide) (by rfl))) hbr
    runBlock T hbr
  | succ k ih =>
    intro D v14 v15 hks hkd hk64 hdo hdv
    have T := mm_iter base dst src S hsal hdal hso hsv D (k + 1) v14 v15 hks hkd hdo hdv
    have hbr := cpsBranchWithin_takenStripPure2
      (bne_spec_gen_within .x12 .x0 0x1fec#13 (BitVec.ofNat 64 (k + 1)) 0 (base + 36))
      (fun hp hq => ofNat_ne_zero k hk64 (pure_end2 hp hq))
    have e1 : base + 36 + signExtend13 0x1fec#13 = base + 16 := by rv64_addr
    rw [e1] at hbr
    have hbr := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 9 (base + 36) (by decide) (by decide) (by rfl))) hbr
    have first : cpsTripleWithin 6 (base + 16) (base + 16) (CodeReq.ofProg base Image.f_memmove.prog)
        ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) ** (.x12 ↦ᵣ BitVec.ofNat 64 (k + 1 + 1)) **
         (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** bytesRegion src S ** bytesRegion dst D)
        ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) ** (.x12 ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         (.x14 ↦ᵣ ((S[k + 1]).zeroExtend 64)) ** (.x15 ↦ᵣ (dst + BitVec.ofNat 64 (k + 1))) **
         bytesRegion src S ** bytesRegion dst (D.set (k + 1) S[k + 1])) := by
      runBlock T hbr
    have hl : (D.set (k + 1) S[k + 1]).length = D.length := List.length_set
    have rest := ih (D.set (k + 1) S[k + 1]) ((S[k + 1]).zeroExtend 64)
      (dst + BitVec.ofNat 64 (k + 1)) (by omega) (by rw [hl]; omega) (by omega)
      (by rw [hl]; exact hdo) (by rw [hl]; exact hdv)
    rw [take_set_drop S D (k + 1) hks hkd] at rest
    exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr first rest)

include hsal hdal hso hsv in
/-- `memmove(dst, src, k + 1)` with `src` below `dst`: the first `k + 1` bytes
    at `dst` become those at `src`, and control returns to the caller. -/
theorem memmove_back (hpos : 0 < S.length) (k : Nat) (D : List (BitVec 8)) (ra v14 v15 : Word)
    (hks : k < S.length) (hkd : k < D.length) (hk64 : k + 1 < 2 ^ 64)
    (hdo : dst.toNat + D.length ≤ 2 ^ 64)
    (hdv : ∀ i, i < D.length → isValidByteAccess (dst + BitVec.ofNat 64 i) = true)
    (hlt : BitVec.ult src dst) :
    cpsTripleWithin (6 * (k + 1) + 5) base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_memmove.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
       (.x12 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
       bytesRegion src S ** bytesRegion dst D)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
       (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (.x14 ↦ᵣ ((S[0]'hpos).zeroExtend 64)) **
       (.x15 ↦ᵣ (dst + BitVec.ofNat 64 0)) **
       bytesRegion src S ** bytesRegion dst (S.take (k + 1) ++ D.drop (k + 1))) := by
  have h0 := mm_head 0x000#12 0x000#12 base dst src v14 v15
  have hb1 := cpsBranchWithin_ntakenStripPure2
    (bgeu_spec_gen_within .x11 .x10 0x0024#13 src dst (base + 8))
    (fun hp hq => (pure_end2 hp hq) hlt)
  have hb2 := cpsBranchWithin_ntakenStripPure2
    (beq_spec_gen_within .x12 .x0 0x0040#13 (BitVec.ofNat 64 (k + 1)) 0 (base + 12))
    (fun hp hq => ofNat_ne_zero k hk64 (pure_end2 hp hq))
  have hl := mm_loop base dst src S hsal hdal hso hsv hpos k D (dst + signExtend12 0x000#12)
    (src + signExtend12 0x000#12) hks hkd (by omega) hdo hdv
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 40)
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_memmove.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hb1 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 2 (base + 8) (by decide) (by decide) (by rfl))) hb1
  have hb2 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hb2
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memmove.prog 10 (base + 40) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hb1 hb2 hl hj

end

/-! ## Thirty-two bytes, as four doublewords -/

/-- The eight bytes of a doubleword, least significant first. -/
def dwBytes (w : Word) : List (BitVec 8) :=
  [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3,
   extractByte w 4, extractByte w 5, extractByte w 6, extractByte w 7]

theorem packBytes_dwBytes (w : Word) : packBytes (dwBytes w) = w := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes _ j hj (by simp [dwBytes]; omega)]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> subst h <;> rfl

/-- The bytes of four doublewords. -/
def bytes4 (w0 w1 w2 w3 : Word) : List (BitVec 8) :=
  dwBytes w0 ++ dwBytes w1 ++ dwBytes w2 ++ dwBytes w3

theorem bytes4_length (w0 w1 w2 w3 : Word) : (bytes4 w0 w1 w2 w3).length = 32 := rfl

theorem bytesRegion_dw (X w : Word) (tl : List (BitVec 8)) :
    bytesRegion X (dwBytes w ++ tl) = ((X ↦ₘ w) ** bytesRegion (X + 8) tl) := by
  rw [bytesRegion_eq_cons X _ (by simp [dwBytes])]
  have e1 : (dwBytes w ++ tl).take 8 = dwBytes w := by simp [dwBytes]
  have e2 : (dwBytes w ++ tl).drop 8 = tl := by simp [dwBytes]
  rw [e1, e2, packBytes_dwBytes]

theorem bytesRegion_bytes4 (X w0 w1 w2 w3 : Word) :
    bytesRegion X (bytes4 w0 w1 w2 w3) = words X [w0, w1, w2, w3] := by
  have e : bytes4 w0 w1 w2 w3 = dwBytes w0 ++ (dwBytes w1 ++ (dwBytes w2 ++ (dwBytes w3 ++ []))) := by
    simp [bytes4]
  rw [e, bytesRegion_dw, bytesRegion_dw, bytesRegion_dw, bytesRegion_dw]
  simp only [bytesRegion_nil, words_cons, words_nil]

theorem memmove32 (base dst src ra v14 v15 s0 s1 s2 s3 d0 d1 d2 d3 : Word)
    (hsal : src.toNat % 8 = 0) (hdal : dst.toNat % 8 = 0)
    (hso : src.toNat + 32 ≤ 2 ^ 64) (hdo : dst.toNat + 32 ≤ 2 ^ 64)
    (hsv : ∀ i, i < 32 → isValidByteAccess (src + BitVec.ofNat 64 i) = true)
    (hdv : ∀ i, i < 32 → isValidByteAccess (dst + BitVec.ofNat 64 i) = true)
    (hlt : BitVec.ult src dst) :
    cpsTripleWithin 197 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_memmove.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
       (.x12 ↦ᵣ BitVec.ofNat 64 32) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
       words src [s0, s1, s2, s3] ** words dst [d0, d1, d2, d3])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
       (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (.x14 ↦ᵣ ((extractByte s0 0).zeroExtend 64)) **
       (.x15 ↦ᵣ (dst + BitVec.ofNat 64 0)) **
       words src [s0, s1, s2, s3] ** words dst [s0, s1, s2, s3]) := by
  have T := memmove_back base dst src (bytes4 s0 s1 s2 s3) hsal hdal hso hsv (by rw [bytes4_length]; omega) 31
    (bytes4 d0 d1 d2 d3) ra v14 v15 (by rw [bytes4_length]; omega) (by rw [bytes4_length]; omega)
    (by decide) hdo hdv hlt
  have e : (bytes4 s0 s1 s2 s3).take (31 + 1) ++ (bytes4 d0 d1 d2 d3).drop (31 + 1) =
      bytes4 s0 s1 s2 s3 := rfl
  rw [e, bytesRegion_bytes4, bytesRegion_bytes4, bytesRegion_bytes4] at T
  exact T

end PureInterp.Handlers
