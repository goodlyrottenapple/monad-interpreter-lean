import PureInterp.Machine.Push1Region
import PureInterp.Machine.PopStep

/-!
# PUSH1 against the invariant
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

/-- Four cells in the middle of an array. -/
theorem words_mid4 (bottom : Word) (P Q : List Word) (c0 c1 c2 c3 : Word) :
    words bottom (P ++ [c0, c1, c2, c3] ++ Q) =
      (words bottom P **
       (((bottom + BitVec.ofNat 64 (8 * P.length)) ↦ₘ c0) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 8) ↦ₘ c1) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 16) ↦ₘ c2) **
        ((bottom + BitVec.ofNat 64 (8 * P.length) + 24) ↦ₘ c3)) **
       words (bottom + BitVec.ofNat 64 (8 * P.length) + BitVec.ofNat 64 (8 * 4)) Q) := by
  rw [List.append_assoc, words_append, words_append]
  have e2 : bottom + BitVec.ofNat 64 (8 * P.length) + 8 + 8 =
      bottom + BitVec.ofNat 64 (8 * P.length) + 16 := by bv_omega
  have e3 : bottom + BitVec.ofNat 64 (8 * P.length) + 16 + 8 =
      bottom + BitVec.ofNat 64 (8 * P.length) + 24 := by bv_omega
  simp only [words_cons, words_nil, sepConj_emp_right', e2, e3, sepConj_assoc']
  rfl

theorem limbsOf_byte (x : BitVec 8) :
    limbsOf (x.zeroExtend 256) = [x.zeroExtend 64, 0, 0, 0] := by
  simp only [limbsOf, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- The handlers' "room for one more word" test. -/
theorem room_ok (bottom : Word) (n : Nat) (hn : n ≤ 1023) :
    ¬ BitVec.slt ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (bottom + BitVec.ofNat 64 (32 * n) - bottom) := by
  have e1 : (((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12 = BitVec.ofNat 64 32736 := by decide
  have e2 : bottom + BitVec.ofNat 64 (32 * n) - bottom = BitVec.ofNat 64 (32 * n) := by bv_omega
  rw [e1, e2, BitVec.slt_iff_toInt_lt]
  simp [BitVec.toInt_eq_toNat_cond]
  omega

/-- The slot above the top of the stack, and what pushing a word does to the
    array. -/
theorem rep_push (limbs : List Word) (stack : List Model.Word256) (w : Model.Word256)
    (h : Rep limbs stack) (hroom : stack.length < 1024) :
    ∃ P Q c0 c1 c2 c3, limbs = P ++ [c0, c1, c2, c3] ++ Q ∧ P.length = 4 * stack.length ∧
      Rep (P ++ limbsOf w ++ Q) (w :: stack) := by
  have hs := h.size
  have hlen : (stack.reverse.flatMap limbsOf).length = 4 * stack.length := by
    rw [flatMap_limbs_length, List.length_reverse]
  have hPl : (limbs.take (4 * stack.length)).length = 4 * stack.length := by
    rw [List.length_take]; omega
  refine ⟨limbs.take (4 * stack.length), limbs.drop (4 * stack.length + 4),
    limbs[4 * stack.length]'(by omega), limbs[4 * stack.length + 1]'(by omega),
    limbs[4 * stack.length + 2]'(by omega), limbs[4 * stack.length + 3]'(by omega), ?_, hPl, ?_⟩
  · apply List.ext_getElem
    · simp; try omega
    · intro i h1 h2
      simp only [List.getElem_append, List.length_take, List.length_append, List.length_cons,
        List.length_nil, List.getElem_take, List.getElem_drop]
      have hm : min (4 * stack.length) limbs.length = 4 * stack.length := by omega
      simp only [hm]
      split
      · split
        · rfl
        · rename_i h3 h4
          have : i - 4 * stack.length < 4 := by omega
          have hi : i = 4 * stack.length ∨ i = 4 * stack.length + 1 ∨ i = 4 * stack.length + 2 ∨
              i = 4 * stack.length + 3 := by omega
          rcases hi with rfl | rfl | rfl | rfl <;> simp
      · congr 1; omega
  · refine ⟨?_, by simp only [List.length_cons]; omega, ?_⟩
    · simp [limbsOf, hs]; omega
    · simp only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [← h.live]
      have h4 : 4 * (stack.length + 1) = (limbs.take (4 * stack.length) ++ limbsOf w).length := by
        simp [limbsOf]; omega
      rw [h4, List.take_left]

theorem push1_step (L : Layout) (scr : Scratch) (limbs : List Word) (base h : Word)
    (stack : List Model.Word256) (gas pc : Nat)
    (hrep : Rep limbs stack) (hroom : stack.length < 1024)
    (hg : 3 ≤ gas) (hgb : gas < 2 ^ 63)
    (hal : L.codeBase.toNat % 8 = 0) (hpc : pc + 2 < L.code.length)
    (hover : L.codeBase.toNat + (pc + 2) < 2 ^ 64)
    (hvalid1 : isValidByteAccess ((L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12) = true)
    (hvalid2 : isValidByteAccess ((L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x002#12) = true)
    (htl : L.table.length = 256)
    (htbl : base + (56 : Word) + (((0x1fffa#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xd0c#12 = L.tbl)
    (hh : L.table[(L.code[pc + 2]'(by omega)).toNat]'(by have := (L.code[pc + 2]'(by omega)).isLt; omega) = h) :
    ∃ scr' limbs', Rep limbs' (((L.code[pc + 1]'(by omega)).zeroExtend 256) :: stack) ∧
      cpsTripleWithin 24 base ((h + signExtend12 0x000#12) &&& ~~~1)
        (CodeReq.ofProg base Image.f_push_1.prog)
        (interp L scr limbs stack.length gas pc)
        (interp L scr' limbs' (stack.length + 1) (gas - 3) (pc + 2)) := by
  obtain ⟨P, Q, c0, c1, c2, c3, hsplit, hPlen, hrep'⟩ := rep_push limbs stack ((L.code[pc + 1]'(by omega)).zeroExtend 256) hrep hroom
  rw [limbsOf_byte] at hrep'
  have hopc := (L.code[pc + 2]'(by omega)).isLt
  have htat := words_at L.tbl L.table (L.code[pc + 2]'(by omega)).toNat (by omega)
  rw [hh] at htat
  obtain ⟨hgas, hgeq⟩ := charge_ok gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb hg
  have hroom' := room_ok L.bottom stack.length (by omega)
  obtain ⟨X, hX⟩ : ∃ X, L.bottom + BitVec.ofNat 64 (8 * P.length) = X := ⟨_, rfl⟩
  have hX' : (L.bottom + BitVec.ofNat 64 (32 * stack.length)) = X := by rw [← hX, hPlen]; congr 2; omega
  have e_t0 : (L.bottom + BitVec.ofNat 64 (32 * stack.length)) + signExtend12 0x000#12 = X := by rw [se_000, hX']; exact BitVec.add_zero _
  have e_t1 : (L.bottom + BitVec.ofNat 64 (32 * stack.length)) + signExtend12 0x008#12 = X + 8 := by
    have : signExtend12 0x008#12 = (8 : Word) := by decide
    rw [hX', this]
  have e_t2 : (L.bottom + BitVec.ofNat 64 (32 * stack.length)) + signExtend12 0x010#12 = X + 16 := by
    have : signExtend12 0x010#12 = (16 : Word) := by decide
    rw [hX', this]
  have e_t3 : (L.bottom + BitVec.ofNat 64 (32 * stack.length)) + signExtend12 0x018#12 = X + 24 := by
    have : signExtend12 0x018#12 = (24 : Word) := by decide
    rw [hX', this]
  have e_top : (L.bottom + BitVec.ofNat 64 (32 * stack.length)) + signExtend12 0x020#12 =
      L.bottom + BitVec.ofNat 64 (32 * (stack.length + 1)) := by
    have : signExtend12 0x020#12 = BitVec.ofNat 64 32 := by decide
    rw [this, ofNat_add_ofNat]; congr 2
  have e_ip : (L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x002#12 = L.codeBase + BitVec.ofNat 64 (pc + 2) := by
    simp only [se_002, ofNat_add_ofNat]
  have e_tc : L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 2]'(by omega)).toNat) + signExtend12 0x000#12 =
      L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 2]'(by omega)).toNat) := by
    rw [se_000]; exact BitVec.add_zero _
  have hent : base + (56 : Word) + (((0x1fffa#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xd0c#12 +
      (((L.code[pc + 2]'(by omega)).zeroExtend 64) <<< (0x03#6).toNat) =
      L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 2]'(by omega)).toNat) := by
    rw [opcode_shl3, htbl]
  have raw := push1_region base L.sp L.ra scr.slot (BitVec.ofNat 64 gas) (L.bottom + BitVec.ofNat 64 (32 * stack.length)) L.bottom L.codeBase
    (L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 2]'(by omega)).toNat)) h scr.r16 scr.r17 L.code pc
    c0 c1 c2 c3 (frameSlot L.sp) X (X + 8) (X + 16) (X + 24)
    (L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 2]'(by omega)).toNat))
    rfl e_t0 e_t1 e_t2 e_t3 e_tc hgas hroom' hal hpc hover hvalid1 hvalid2 hent
  rw [opcode_shl3, hgeq, e_top, e_ip, frame_restore] at raw
  refine ⟨⟨scr.r5, scr.r6, h, BitVec.ofNat 64 (8 * (L.code[pc + 2]'(by omega)).toNat), scr.r28, scr.r29, scr.r30, scr.r31, L.ra, scr.r7⟩,
    P ++ [((L.code[pc + 1]'(by omega)).zeroExtend 64), 0, 0, 0] ++ Q, hrep', ?_⟩
  have hw1 := words_mid4 L.bottom P Q c0 c1 c2 c3
  rw [← hsplit] at hw1
  have hw2 := words_mid4 L.bottom P Q ((L.code[pc + 1]'(by omega)).zeroExtend 64) 0 0 0
  rw [hX] at hw1 hw2
  unfold interp
  rw [hw1, hw2, htat]
  have raw' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ scr.r5) ** (.x6 ↦ᵣ scr.r6) ** (.x7 ↦ᵣ scr.r7) ** (.x28 ↦ᵣ scr.r28) ** (.x29 ↦ᵣ scr.r29) **
      (.x30 ↦ᵣ scr.r30) ** (.x31 ↦ᵣ scr.r31) ** words L.bottom P **
      words (X + BitVec.ofNat 64 (8 * 4)) Q **
      words L.tbl (L.table.take (L.code[pc + 2]'(by omega)).toNat) **
      words (L.tbl + BitVec.ofNat 64 (8 * ((L.code[pc + 2]'(by omega)).toNat + 1))) (L.table.drop ((L.code[pc + 2]'(by omega)).toNat + 1)))
    (by pcFree) raw
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) raw'

end PureInterp.Machine
