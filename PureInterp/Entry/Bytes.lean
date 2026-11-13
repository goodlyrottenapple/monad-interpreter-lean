import PureInterp.Entry.Basic

/-!
# Byte regions: stores at an offset, overwriting a range

The library's `bytesRegion_sb_within` / `bytesRegion_lbu_within` are stated
for offset 0. `sb_region_at` / `lbu_region_at` restate them for any pointer and
offset whose sum is `regionBase + i` (the proofs are the library's, with the
address equation as a hypothesis).

`splice bs i xs` is `bs` with the bytes from index `i` replaced by `xs`; the
byte loops (`memset`, `memcpy`) are stated with it.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

instance (base : Word) (bs : List (BitVec 8)) : Assertion.PCFree (bytesRegion base bs) :=
  ⟨bytesRegion_pcFree base bs⟩

/-- `SB rs1 rs2 off` storing to byte `i` of an aligned region. -/
theorem sb_region_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word) (off : BitVec 12)
    (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 off = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 off))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
       bytesRegion regionBase (bs.set i (v_data.truncate 8))) := by
  have hr : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_set regionBase bs (i / 8) (i % 8) (v_data.truncate 8) hr (by omega)
  rw [hi_eq] at heqset
  have halign' : alignToDword (ptr + signExtend12 off)
      = regionBase + BitVec.ofNat 64 (8 * (i / 8)) := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' : isValidByteAccess (ptr + signExtend12 off) = true := by
    rw [hptr]; exact hvalid
  have sb := generic_sb_spec_within rs1 rs2 ptr v_data off base
    (regionBase + BitVec.ofNat 64 (8 * (i / 8))) (packBytes ((bs.drop (8 * (i / 8))).take 8))
    halign' hvalid'
  have hbo : byteOffset (ptr + signExtend12 off) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 < ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, packBytes_set _ (i % 8) (v_data.truncate 8) hr hchunk_len] at sb
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sb)

/-- `LBU rd rs1 off` loading byte `i` of an aligned region. -/
theorem lbu_region_at (rd rs1 : Reg) (regionBase ptr vOld : Word) (off : BitVec 12)
    (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 off = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 off))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** bytesRegion regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs (i / 8) hq
  have halign' : alignToDword (ptr + signExtend12 off)
      = regionBase + BitVec.ofNat 64 (8 * (i / 8)) := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' : isValidByteAccess (ptr + signExtend12 off) = true := by
    rw [hptr]; exact hvalid
  have lbu := generic_lbu_spec_within rd rs1 ptr vOld off base
    (regionBase + BitVec.ofNat 64 (8 * (i / 8))) (packBytes ((bs.drop (8 * (i / 8))).take 8))
    hrd halign' hvalid'
  have hbyte : extractByte (packBytes ((bs.drop (8 * (i / 8))).take 8))
      (byteOffset (ptr + signExtend12 off)) = bs[i]'hi := by
    rw [hptr, byteOffset_add_ofNat_of_aligned halign hover,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

/-! ## Overwriting a range -/

/-- `bs` with the bytes from index `i` replaced by `xs`. -/
def splice (bs : List (BitVec 8)) (i : Nat) (xs : List (BitVec 8)) : List (BitVec 8) :=
  bs.take i ++ xs ++ bs.drop (i + xs.length)

@[simp] theorem splice_nil (bs : List (BitVec 8)) (i : Nat) : splice bs i [] = bs := by
  simp [splice]

theorem splice_length (bs : List (BitVec 8)) (i : Nat) (xs : List (BitVec 8))
    (h : i + xs.length ≤ bs.length) : (splice bs i xs).length = bs.length := by
  simp [splice]; omega

/-- Writing one more byte just past the spliced range extends the range. -/
theorem splice_set (bs : List (BitVec 8)) (i : Nat) (xs : List (BitVec 8)) (b : BitVec 8)
    (h : i + xs.length < bs.length) :
    (splice bs i xs).set (i + xs.length) b = splice bs i (xs ++ [b]) := by
  unfold splice
  have hl : (bs.take i ++ xs).length = i + xs.length := by simp; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self,
    List.drop_eq_getElem_cons h, List.set_cons_zero]
  simp [Nat.add_assoc]

/-! ## Pointer arithmetic -/

theorem ptr_succ (b : Word) (i : Nat) :
    b + BitVec.ofNat 64 i + signExtend12 0x001#12 = b + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 0x001#12 = (1 : Word) from by decide, BitVec.add_assoc, BitVec.ofNat_add]
  rfl

theorem ptr_add (b : Word) (i n : Nat) :
    b + BitVec.ofNat 64 i + BitVec.ofNat 64 n = b + BitVec.ofNat 64 (i + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ptr_pred (b : Word) (i : Nat) :
    b + BitVec.ofNat 64 (i + 1) + signExtend12 0xfff#12 = b + BitVec.ofNat 64 i := by
  rw [show signExtend12 0xfff#12 = (-1 : Word) from by decide, BitVec.ofNat_add]
  bv_omega

/-- Distinct in-range offsets give distinct pointers. -/
theorem ptr_ne (b : Word) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (hne : i ≠ j) :
    b + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j := by
  intro h
  have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
    have := congrArg (fun x => x - b) h
    simpa using this
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at this
  omega

end PureInterp.Entry
