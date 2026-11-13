import PureInterp.Machine.Lemmas
import PureInterp.Handlers.Pop

/-!
# POP against the invariant
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

/-- The handlers' "at least one operand" test. -/
theorem depth1_ok (bottom : Word) (n : Nat) (hn : n ≤ 1023) :
    BitVec.slt (0 : Word) (bottom + BitVec.ofNat 64 (32 * (n + 1)) - bottom) := by
  have e2 : bottom + BitVec.ofNat 64 (32 * (n + 1)) - bottom = BitVec.ofNat 64 (32 * (n + 1)) := by
    bv_omega
  rw [e2, BitVec.slt_iff_toInt_lt]
  simp [BitVec.toInt_eq_toNat_cond]
  omega

theorem flatMap_limbs_length (ws : List Model.Word256) :
    (ws.flatMap limbsOf).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons x xs ih => simp [limbsOf] at ih ⊢; omega

/-- Dropping the top word keeps the array a representation of the rest. -/
theorem rep_pop (limbs : List Word) (a : Model.Word256) (rest : List Model.Word256)
    (h : Rep limbs (a :: rest)) : Rep limbs rest := by
  have hl := h.live
  have hd := h.depth
  simp only [List.length_cons, List.reverse_cons, List.flatMap_append] at hl hd
  refine ⟨h.size, by omega, ?_⟩
  have hlen : (rest.reverse.flatMap limbsOf).length = 4 * rest.length := by
    rw [flatMap_limbs_length, List.length_reverse]
  have := congrArg (List.take (4 * rest.length)) hl
  rw [List.take_take, Nat.min_eq_left (by omega),
    List.take_append_of_le_length (by omega)] at this
  rw [this, ← hlen, List.take_length]

theorem pop_step (L : Layout) (scr : Scratch) (limbs : List Word) (base h : Word)
    (a : Model.Word256) (rest : List Model.Word256) (gas pc : Nat)
    (hrep : Rep limbs (a :: rest))
    (hg : 2 ≤ gas) (hgb : gas < 2 ^ 63)
    (hal : L.codeBase.toNat % 8 = 0) (hpc : pc + 1 < L.code.length)
    (hover : L.codeBase.toNat + (pc + 1) < 2 ^ 64)
    (hvalid : isValidByteAccess ((L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12) = true)
    (htl : L.table.length = 256)
    (htbl : base + (28 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xca8#12 = L.tbl)
    (hh : L.table[(L.code[pc + 1]).toNat]'(by have := (L.code[pc + 1]).isLt; omega) = h) :
    ∃ scr', Rep limbs rest ∧
      cpsTripleWithin 17 base ((h + signExtend12 0x000#12) &&& ~~~1)
        (CodeReq.ofProg base Image.f_pop.prog)
        (interp L scr limbs (rest.length + 1) gas pc)
        (interp L scr' limbs rest.length (gas - 2) (pc + 1)) := by
  obtain ⟨cwAddr, cw, cf, crest, hcf, hcr, hceq, hcal, hcbyte⟩ :=
    code_cell L.codeBase L.code pc 1 0x001#12 se_001 hal hpc hover
  have hopc := (L.code[pc + 1]).isLt
  have htat := words_at L.tbl L.table (L.code[pc + 1]).toNat (by omega)
  rw [hh] at htat
  obtain ⟨hgas, hgeq⟩ := charge_ok gas 2 0xffe#12 (by omega) (by omega) (by decide) hgb hg
  have hd := hrep.depth
  simp only [List.length_cons] at hd
  have hdepth := depth1_ok L.bottom rest.length (by omega)
  have e_top : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 1))) + signExtend12 0xfe0#12 = L.bottom + BitVec.ofNat 64 (32 * rest.length) := by
    rw [se_fe0]
    have := top_sub L.bottom (rest.length + 1) 32 (by omega) (by omega)
    rw [this]; congr 2
  have e_ip : (L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12 = L.codeBase + BitVec.ofNat 64 (pc + 1) := by
    simp only [se_001, ofNat_add_ofNat]
  have e_tc : L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat) + signExtend12 0x000#12 =
      L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat) := by
    rw [se_000]; exact BitVec.add_zero _
  have hent : base + (28 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xca8#12 +
      (((extractByte cw (byteOffset ((L.codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12))).zeroExtend 64) <<<
        (0x03#6).toNat) = L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat) := by
    rw [hcbyte, opcode_shl3, htbl]
  have raw := pop_spec base L.sp L.ra scr.slot (BitVec.ofNat 64 gas) (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 1))) L.bottom (L.codeBase + BitVec.ofNat 64 pc) cw cwAddr
    (L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat)) h scr.r16 scr.r17 (frameSlot L.sp)
    (L.tbl + BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat)) rfl e_tc hgas hdepth hcal hvalid hent
  rw [hcbyte, opcode_shl3, hgeq, e_top, e_ip, frame_restore] at raw
  refine ⟨⟨scr.r5, scr.r6, h, BitVec.ofNat 64 (8 * (L.code[pc + 1]).toNat), scr.r28, scr.r29, scr.r30, scr.r31, L.ra, scr.r7⟩,
    rep_pop limbs a rest hrep, ?_⟩
  unfold interp
  rw [hceq, htat]
  have raw' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ scr.r5) ** (.x6 ↦ᵣ scr.r6) ** (.x7 ↦ᵣ scr.r7) ** (.x28 ↦ᵣ scr.r28) ** (.x29 ↦ᵣ scr.r29) **
      (.x30 ↦ᵣ scr.r30) ** (.x31 ↦ᵣ scr.r31) ** words L.bottom limbs ** cf ** crest **
      words L.tbl (L.table.take (L.code[pc + 1]).toNat) **
      words (L.tbl + BitVec.ofNat 64 (8 * ((L.code[pc + 1]).toNat + 1))) (L.table.drop ((L.code[pc + 1]).toNat + 1)))
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (words_pcFree _ _) (pcFree_sepConj hcf (pcFree_sepConj hcr
        (pcFree_sepConj (words_pcFree _ _) (words_pcFree _ _)))))))))))) raw
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) raw'

end PureInterp.Machine
