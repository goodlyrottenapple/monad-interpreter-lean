import PureInterp.Machine.Lemmas
import PureInterp.Handlers.Sub

/-!
# SUB against the invariant

`sub_step` is the SUB handler theorem in the form the simulation loop uses:
from the invariant for a model state with `a :: b :: rest` on the stack and at
least 3 gas, the machine reaches the handler of the next opcode with the
invariant for the state `Model.step` produces, whose top word is `a - b`.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

/-- The limbs the SUB handler computes are the limbs of the difference. -/
theorem limbsOf_sub (a b : BitVec 256) :
    limbsOf (a - b) =
      [ ((a.extractLsb' 0 64) - (b.extractLsb' 0 64)),
        ((a.extractLsb' 64 64) - (b.extractLsb' 64 64) - cb (a.extractLsb' 0 64) (b.extractLsb' 0 64)),
        ((a.extractLsb' 128 64) - (b.extractLsb' 128 64) - (cb (a.extractLsb' 64 64) (b.extractLsb' 64 64) ||| cb ((a.extractLsb' 64 64) - (b.extractLsb' 64 64)) (cb (a.extractLsb' 0 64) (b.extractLsb' 0 64)))),
        ((a.extractLsb' 192 64) - (b.extractLsb' 192 64) - (cb (a.extractLsb' 128 64) (b.extractLsb' 128 64) ||| cb ((a.extractLsb' 128 64) - (b.extractLsb' 128 64)) (cb (a.extractLsb' 64 64) (b.extractLsb' 64 64) ||| cb ((a.extractLsb' 64 64) - (b.extractLsb' 64 64)) (cb (a.extractLsb' 0 64) (b.extractLsb' 0 64))))) ] := by
  simp only [limbsOf, cb, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem sub_step (L : Layout) (scr : Scratch) (limbs : List Word) (base h : Word)
    (a b : Model.Word256) (rest : List Model.Word256) (gas pc : Nat)
    (hrep : Rep limbs (a :: b :: rest))
    (hg3 : 3 ≤ gas) (hgb : gas < 2 ^ 63)
    (hal : L.codeBase.toNat % 8 = 0) (hpc : pc + 1 < L.code.length)
    (hover : L.codeBase.toNat + (pc + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess ((L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12) = true)
    (htl : L.table.length = 256)
    (htbl : base + (136 : Word) + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0x30c#12 = L.tbl)
    (hh : L.table[(L.code[pc + 1]).toNat]'(by have := (L.code[pc + 1]).isLt; omega) = h) :
    ∃ scr' limbs', Rep limbs' ((a - b) :: rest) ∧
      cpsTripleWithin 44 base ((h + signExtend12 0x000#12) &&& ~~~1)
        (CodeReq.ofProg base Image.f_sub.prog)
        (interp L scr limbs (rest.length + 2) gas pc)
        (interp L scr' limbs' (rest.length + 1) (gas - 3) (pc + 1)) := by
  obtain ⟨hsplit, hPlen, hP⟩ := rep_split2 limbs a b rest hrep
  obtain ⟨cwAddr, cw, cf, crest, hcf, hcr, hceq, hcal, hcbyte⟩ :=
    code_cell L.codeBase L.code pc 1 0x001#12 se_001 hal hpc hover
  have hopc := (L.code[pc + 1]).isLt
  have htat := words_at L.tbl L.table (L.code[pc + 1]).toNat (by omega)
  rw [hh] at htat
  -- name the limbs
  obtain ⟨a0, ha0⟩ : ∃ x, a.extractLsb' 0 64 = x := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ x, a.extractLsb' 64 64 = x := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ x, a.extractLsb' 128 64 = x := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ x, a.extractLsb' 192 64 = x := ⟨_, rfl⟩
  obtain ⟨b0, hb0⟩ : ∃ x, b.extractLsb' 0 64 = x := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ x, b.extractLsb' 64 64 = x := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ x, b.extractLsb' 128 64 = x := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ x, b.extractLsb' 192 64 = x := ⟨_, rfl⟩
  have hsum := limbsOf_sub a b
  rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at hsum
  have hlab : limbsOf b ++ limbsOf a = [b0, b1, b2, b3, a0, a1, a2, a3] := by
    simp [limbsOf, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
  rw [hlab] at hsplit
  obtain ⟨P, hPdef⟩ : ∃ P, limbs.take (4 * rest.length) = P := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, limbs.drop (4 * (rest.length + 2)) = Q := ⟨_, rfl⟩
  rw [hPdef] at hsplit hPlen hP
  rw [hQdef] at hsplit
  -- gas, depth, addresses
  obtain ⟨hgas, hgeq⟩ := charge_ok gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb hg3
  have hd := hrep.depth
  simp only [List.length_cons] at hd
  have hdepth := depth2_ok L.bottom rest.length (by omega)
  obtain ⟨X, hX⟩ : ∃ X, L.bottom + BitVec.ofNat 64 (8 * P.length) = X := ⟨_, rfl⟩
  have hX' : L.bottom + BitVec.ofNat 64 (8 * (4 * rest.length)) = X := by rw [← hX, hPlen]
  have e_m0 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfc0#12 = X := by
    rw [se_fc0, ← hX']
    have := slot_addr L.bottom rest.length 64 0 (by omega) (by omega)
    rw [this]; exact BitVec.add_zero _
  have e_m1 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfc8#12 = X + 8 := by
    rw [se_fc8, ← hX']; exact slot_addr L.bottom rest.length 56 8 (by omega) (by omega)
  have e_m2 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfd0#12 = X + 16 := by
    rw [se_fd0, ← hX']; exact slot_addr L.bottom rest.length 48 16 (by omega) (by omega)
  have e_m3 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfd8#12 = X + 24 := by
    rw [se_fd8, ← hX']; exact slot_addr L.bottom rest.length 40 24 (by omega) (by omega)
  have e_n0 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfe0#12 = X + 32 := by
    rw [se_fe0, ← hX']; exact slot_addr L.bottom rest.length 32 32 (by omega) (by omega)
  have e_n1 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfe8#12 = X + 40 := by
    rw [se_fe8, ← hX']; exact slot_addr L.bottom rest.length 24 40 (by omega) (by omega)
  have e_n2 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xff0#12 = X + 48 := by
    rw [se_ff0, ← hX']; exact slot_addr L.bottom rest.length 16 48 (by omega) (by omega)
  have e_n3 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xff8#12 = X + 56 := by
    rw [se_ff8, ← hX']; exact slot_addr L.bottom rest.length 8 56 (by omega) (by omega)
  have e_top : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfe0#12 =
      L.bottom + BitVec.ofNat 64 (32 * (rest.length + 1)) := by
    rw [se_fe0]
    have := top_sub L.bottom (rest.length + 2) 32 (by omega) (by omega)
    rw [this]; congr 2
  have e_ip : (L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12 = L.codeBase + BitVec.ofNat 64 (pc + 1) := by
    simp only [se_001, ofNat_add_ofNat]
  have e_tc : L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat) + signExtend12 0x000#12 =
      L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat) := by
    rw [se_000]; exact BitVec.add_zero _
  have hent : base + (136 : Word) + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0x30c#12 +
      (((extractByte cw (byteOffset ((L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12))).zeroExtend 64) <<<
        (0x03#6).toNat) = L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat) := by
    rw [hcbyte, opcode_shl3, htbl]
  have raw := sub_spec base L.sp L.ra scr.slot (BitVec.ofNat 64 gas) (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) L.bottom (L.codeBase + BitVec.ofNat 64 pc) cw cwAddr
    (L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat)) h
    a0 a1 a2 a3 b0 b1 b2 b3 scr.r5 scr.r6 scr.r7 scr.r16 scr.r17 scr.r28 scr.r29 scr.r30 scr.r31
    (frameSlot L.sp) X (X + 8) (X + 16) (X + 24) (X + 32) (X + 40) (X + 48) (X + 56)
    (L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat))
    rfl e_m0 e_m1 e_m2 e_m3 e_n0 e_n1 e_n2 e_n3 e_tc hgas hdepth hcal hvalid hent
  rw [hcbyte, opcode_shl3, hgeq, e_top, e_ip, frame_restore] at raw
  -- the new stack array
  refine ⟨⟨cb a0 b0, (a3 - b3), h, BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat), (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))), (a1 - b1 - cb a0 b0), (a0 - b0), (cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))), L.ra, b3⟩,
    P ++ [(a0 - b0), (a1 - b1 - cb a0 b0), (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))), (a3 - b3 - (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))), a0, a1, a2, a3] ++ Q, ?_, ?_⟩
  · have hs := hrep.size
    have hQlen : Q.length = 4 * 1025 - 4 * (rest.length + 2) := by
      rw [← hQdef, List.length_drop, hs]
    have h4 : 4 * (rest.length + 1) = P.length + 4 := by omega
    refine ⟨?_, by simp only [List.length_cons]; omega, ?_⟩
    · simp [hPlen, hQlen]; omega
    · simp only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [hsum, ← hP, h4, List.append_assoc, List.take_append]
      simp
  · have hw1 := words_mid8 L.bottom P Q b0 b1 b2 b3 a0 a1 a2 a3
    rw [← hsplit] at hw1
    have hw2 := words_mid8 L.bottom P Q (a0 - b0) (a1 - b1 - cb a0 b0) (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))) (a3 - b3 - (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) a0 a1 a2 a3
    rw [hX] at hw1 hw2
    unfold interp
    rw [hw1, hw2, hceq, htat]
    have raw' := cpsTripleWithin_frameR
      (words L.bottom P ** words (X + BitVec.ofNat 64 (8 * 8)) Q ** cf ** crest **
        words L.tbl (L.table.take (L.code[pc + 1]).toNat) **
        words (L.tbl + BitVec.ofNat 64 (8 * ((L.code[pc + 1]).toNat + 1)))
          (L.table.drop ((L.code[pc + 1]).toNat + 1)))
      (pcFree_sepConj (words_pcFree _ _) (pcFree_sepConj (words_pcFree _ _)
        (pcFree_sepConj hcf (pcFree_sepConj hcr
          (pcFree_sepConj (words_pcFree _ _) (words_pcFree _ _)))))) raw
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) raw'

end PureInterp.Machine
