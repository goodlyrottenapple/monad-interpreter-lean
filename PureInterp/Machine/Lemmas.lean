import PureInterp.Machine.Invariant
import PureInterp.Handlers.Add
import Std.Tactic.BVDecide

/-!
# Lemmas for restating handler theorems against the invariant

Each handler theorem names the individual memory cells it touches. These
lemmas take those cells out of the invariant's regions: one bytecode byte, one
instruction-table entry, and the top stack slots.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

/-! ## Bytecode -/

theorem ofNat_add_ofNat (base : Word) (i k : Nat) :
    base + BitVec.ofNat 64 i + BitVec.ofNat 64 k = base + BitVec.ofNat 64 (i + k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The doubleword holding bytecode byte `pc + k`, as the cell a handler's
    `lbu k(a5)` reads, with the byte it yields. -/
theorem code_cell (codeBase : Word) (code : List (BitVec 8)) (pc k : Nat) (ok : BitVec 12)
    (hok : signExtend12 ok = BitVec.ofNat 64 k)
    (hal : codeBase.toNat % 8 = 0) (hi : pc + k < code.length)
    (hover : codeBase.toNat + (pc + k) < 2 ^ 64) :
    ∃ cwAddr cw front rest, front.pcFree ∧ rest.pcFree ∧
      bytesRegion codeBase code = (front ** (cwAddr ↦ₘ cw) ** rest) ∧
      alignToDword (codeBase + BitVec.ofNat 64 pc + signExtend12 ok) = cwAddr ∧
      extractByte cw (byteOffset (codeBase + BitVec.ofNat 64 pc + signExtend12 ok)) = code[pc + k] := by
  have hq : 8 * ((pc + k) / 8) < code.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at codeBase code ((pc + k) / 8) hq
  refine ⟨_, _, front, rest, hf, hr, heq, ?_, ?_⟩
  · rw [hok, ofNat_add_ofNat]
    exact alignToDword_add_ofNat_of_aligned hal hover
  · rw [hok, ofNat_add_ofNat, byteOffset_add_ofNat_of_aligned hal hover,
      extractByte_packBytes _ _ (by omega) (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    congr 1; omega

theorem se_001 : signExtend12 0x001#12 = BitVec.ofNat 64 1 := by decide
theorem se_002 : signExtend12 0x002#12 = BitVec.ofNat 64 2 := by decide
theorem se_000 : signExtend12 0x000#12 = (0 : Word) := by decide

/-! ## Instruction table -/

/-- An opcode byte scaled to a table offset. -/
theorem opcode_shl3 (x : BitVec 8) :
    (x.zeroExtend 64 : Word) <<< (0x03#6).toNat = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-! ## Stack slots -/

/-- Eight consecutive cells with flat addresses. -/
theorem words_8 (X c0 c1 c2 c3 c4 c5 c6 c7 : Word) :
    words X [c0, c1, c2, c3, c4, c5, c6, c7] =
      ((X ↦ₘ c0) ** ((X + 8) ↦ₘ c1) ** ((X + 16) ↦ₘ c2) ** ((X + 24) ↦ₘ c3) **
       ((X + 32) ↦ₘ c4) ** ((X + 40) ↦ₘ c5) ** ((X + 48) ↦ₘ c6) ** ((X + 56) ↦ₘ c7)) := by
  have e2 : X + 8 + 8 = X + 16 := by bv_omega
  have e3 : X + 16 + 8 = X + 24 := by bv_omega
  have e4 : X + 24 + 8 = X + 32 := by bv_omega
  have e5 : X + 32 + 8 = X + 40 := by bv_omega
  have e6 : X + 40 + 8 = X + 48 := by bv_omega
  have e7 : X + 48 + 8 = X + 56 := by bv_omega
  simp only [words_cons, words_nil, sepConj_emp_right', e2, e3, e4, e5, e6, e7]

/-- Address of byte `j` of the two top slots, as a handler computes it from
    the top pointer with a negative offset `-k`. -/
theorem slot_addr (bottom : Word) (n k j : Nat) (hk : k ≤ 64) (hj : j + k = 64) :
    bottom + BitVec.ofNat 64 (32 * (n + 2)) + BitVec.ofNat 64 (2 ^ 64 - k) =
      bottom + BitVec.ofNat 64 (8 * (4 * n)) + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Eight cells in the middle of an array. -/
theorem words_mid8 (bottom : Word) (P Q : List Word) (c0 c1 c2 c3 c4 c5 c6 c7 : Word) :
    words bottom (P ++ [c0, c1, c2, c3, c4, c5, c6, c7] ++ Q) =
      (words bottom P **
       (((bottom + BitVec.ofNat 64 (8 * P.length)) ↦ₘ c0) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 8) ↦ₘ c1) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 16) ↦ₘ c2) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 24) ↦ₘ c3) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 32) ↦ₘ c4) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 40) ↦ₘ c5) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 48) ↦ₘ c6) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 56) ↦ₘ c7)) **
       words (bottom + BitVec.ofNat 64 (8 * P.length) + BitVec.ofNat 64 (8 * 8)) Q) := by
  rw [List.append_assoc, words_append, words_append, words_8]
  rfl

/-- The handlers' gas charge on a counter holding `gas`. -/
theorem charge_ok (gas c : Nat) (imm : BitVec 12) (hc : c < 2048) (hpos : 0 < c)
    (himm : imm = BitVec.ofNat 12 (4096 - c)) (hg : gas < 2 ^ 63) (hle : c ≤ gas) :
    ¬ BitVec.slt (BitVec.ofNat 64 gas + signExtend12 imm) 0 ∧
    BitVec.ofNat 64 gas + signExtend12 imm = BitVec.ofNat 64 (gas - c) := by
  have hn : (BitVec.ofNat 64 gas).toNat = gas := by simp; omega
  obtain ⟨h1, h2⟩ := Refine.gas_charge (BitVec.ofNat 64 gas) c imm hc himm (by omega) hpos
  refine ⟨h1.mpr (by omega), ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [h2 (by omega), hn]
  simp; omega

/-- The handlers' "at least two operands" test. -/
theorem depth2_ok (bottom : Word) (n : Nat) (hn : n ≤ 1022) :
    BitVec.slt ((0 : Word) + signExtend12 0x020#12)
      (bottom + BitVec.ofNat 64 (32 * (n + 2)) - bottom) := by
  have e1 : (0 : Word) + signExtend12 0x020#12 = BitVec.ofNat 64 32 := by decide
  have e2 : bottom + BitVec.ofNat 64 (32 * (n + 2)) - bottom = BitVec.ofNat 64 (32 * (n + 2)) := by
    bv_omega
  rw [e1, e2, BitVec.slt_iff_toInt_lt]
  simp [BitVec.toInt_eq_toNat_cond]
  omega

/-- With two words on top, the stack array splits around their eight limbs. -/
theorem rep_split2 (limbs : List Word) (a b : Model.Word256) (rest : List Model.Word256)
    (h : Rep limbs (a :: b :: rest)) :
    limbs = limbs.take (4 * rest.length) ++ (limbsOf b ++ limbsOf a) ++
      limbs.drop (4 * (rest.length + 2)) ∧ (limbs.take (4 * rest.length)).length = 4 * rest.length ∧
      limbs.take (4 * rest.length) = rest.reverse.flatMap limbsOf := by
  have hl := h.live
  have hs := h.size
  have hd := h.depth
  simp only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc] at hl hd
  have hlen : ((rest.reverse.flatMap limbsOf)).length = 4 * rest.length := by
    induction rest with
    | nil => rfl
    | cons x xs ih => simp [List.flatMap_append, limbsOf] at ih ⊢; omega
  have ht : limbs.take (4 * rest.length) = rest.reverse.flatMap limbsOf := by
    have := congrArg (List.take (4 * rest.length)) hl
    rw [List.take_take, List.take_append_of_le_length (by omega)] at this
    rw [Nat.min_eq_left (by omega)] at this
    rw [this, ← hlen, List.take_length]
  refine ⟨?_, by rw [List.length_take]; omega, ht⟩
  conv => lhs; rw [← List.take_append_drop (4 * (rest.length + 1 + 1)) limbs]
  rw [hl, ht, List.append_assoc]

/-- The limbs the ADD handler computes are the limbs of the sum. -/
theorem limbsOf_add (a b : Model.Word256) :
    limbsOf (a + b) =
      [ b.extractLsb' 0 64 + a.extractLsb' 0 64,
        a.extractLsb' 64 64 + b.extractLsb' 64 64 +
          cb (b.extractLsb' 0 64 + a.extractLsb' 0 64) (b.extractLsb' 0 64),
        a.extractLsb' 128 64 + b.extractLsb' 128 64 +
          (cb (a.extractLsb' 64 64 + b.extractLsb' 64 64) (a.extractLsb' 64 64) |||
           cb (a.extractLsb' 64 64 + b.extractLsb' 64 64 +
             cb (b.extractLsb' 0 64 + a.extractLsb' 0 64) (b.extractLsb' 0 64))
             (a.extractLsb' 64 64 + b.extractLsb' 64 64)),
        a.extractLsb' 192 64 + b.extractLsb' 192 64 +
          (cb (a.extractLsb' 128 64 + b.extractLsb' 128 64) (a.extractLsb' 128 64) |||
           cb (a.extractLsb' 128 64 + b.extractLsb' 128 64 +
             (cb (a.extractLsb' 64 64 + b.extractLsb' 64 64) (a.extractLsb' 64 64) |||
              cb (a.extractLsb' 64 64 + b.extractLsb' 64 64 +
                cb (b.extractLsb' 0 64 + a.extractLsb' 0 64) (b.extractLsb' 0 64))
                (a.extractLsb' 64 64 + b.extractLsb' 64 64)))
             (a.extractLsb' 128 64 + b.extractLsb' 128 64)) ] := by
  simp only [limbsOf, cb, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

end PureInterp.Machine
