import PureInterp.Machine.Fail
import PureInterp.Handlers.Return

/-!
# RETURN against the invariant

`return_final`: from the invariant for a model state with `off :: size :: rest`
on the stack, through `return_`, `return_impl` (two `memmove`s), `Context::exit`
and `longjmp`, to the `setjmp` return site, with status 0 and the gas in the
context and the limbs of `off` and `size` in its `result.offset` and
`result.size` fields. `return_err_final` is the stack-underflow exit.

The handler charges no gas. The memory-expansion charge for the returned range
and the output buffer are made after the interpreter has left, by
`Context::copy_result_data`, from exactly these three context fields.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

/-! ## Lists and addresses -/

theorem list8 {α : Type} (l : List α) (h : l.length = 8) :
    ∃ a b c d e f g i, l = [a, b, c, d, e, f, g, i] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨i, _ | ⟨j, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨a, b, c, d, e, f, g, i, rfl⟩

theorem list10 {α : Type} (l : List α) (h : l.length = 10) :
    ∃ a b c d e f g i j k, l = [a, b, c, d, e, f, g, i, j, k] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨m, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨a, b, c, d, e, f, g, i, j, k, rfl⟩

theorem addr2 (x c1 c2 k : Word) (h : c1 + c2 = k) : x + c1 + c2 = x + k := by
  rw [BitVec.add_assoc, h]

theorem addr3 (x c1 c2 c3 k : Word) (h : c1 + (c2 + c3) = k) : x + c1 + c2 + c3 = x + k := by
  rw [BitVec.add_assoc, BitVec.add_assoc, h]

theorem addr3_zero (x c1 c2 c3 : Word) (h : c1 + (c2 + c3) = 0) : x + c1 + c2 + c3 = x := by
  rw [addr3 x c1 c2 c3 0 h]; exact BitVec.add_zero x

theorem addr2_zero (x c1 c2 : Word) (h : c1 + c2 = 0) : x + c1 + c2 = x := by
  rw [addr2 x c1 c2 0 h]; exact BitVec.add_zero x

/-- From `x + c = y + d`, the base `x` in terms of `y`. -/
theorem addr_shift (x y c d e : Word) (h : x + c = y + d) (he : d - c = e) : x = y + e := by
  have h1 : x = y + d - c := BitVec.eq_sub_iff_add_eq.mpr h
  rw [h1, ← he, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem toNat_add_ofNat' (x : Word) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt h

/-- Ten consecutive cells with flat addresses. -/
theorem words_10 (X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Word) :
    words X [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] =
      ((X ↦ₘ c0) ** ((X + 8) ↦ₘ c1) ** ((X + 16) ↦ₘ c2) ** ((X + 24) ↦ₘ c3) **
       ((X + 32) ↦ₘ c4) ** ((X + 40) ↦ₘ c5) ** ((X + 48) ↦ₘ c6) ** ((X + 56) ↦ₘ c7) **
       ((X + 64) ↦ₘ c8) ** ((X + 72) ↦ₘ c9)) := by
  have e2 : X + 8 + 8 = X + 16 := addr2 _ _ _ _ (by decide)
  have e3 : X + 16 + 8 = X + 24 := addr2 _ _ _ _ (by decide)
  have e4 : X + 24 + 8 = X + 32 := addr2 _ _ _ _ (by decide)
  have e5 : X + 32 + 8 = X + 40 := addr2 _ _ _ _ (by decide)
  have e6 : X + 40 + 8 = X + 48 := addr2 _ _ _ _ (by decide)
  have e7 : X + 48 + 8 = X + 56 := addr2 _ _ _ _ (by decide)
  have e8 : X + 56 + 8 = X + 64 := addr2 _ _ _ _ (by decide)
  have e9 : X + 64 + 8 = X + 72 := addr2 _ _ _ _ (by decide)
  simp only [words_cons, words_nil, sepConj_emp_right', e2, e3, e4, e5, e6, e7, e8, e9]

/-- Two four-cell words in the middle of an array. -/
theorem words_mid44 (bottom : Word) (P Q : List Word) (c0 c1 c2 c3 c4 c5 c6 c7 : Word) :
    words bottom (P ++ [c0, c1, c2, c3, c4, c5, c6, c7] ++ Q) =
      (words bottom P **
       (words (bottom + BitVec.ofNat 64 (8 * P.length)) [c0, c1, c2, c3] **
        words (bottom + BitVec.ofNat 64 (8 * P.length) + 32) [c4, c5, c6, c7]) **
       words (bottom + BitVec.ofNat 64 (8 * P.length) + BitVec.ofNat 64 (8 * 8)) Q) := by
  rw [List.append_assoc, words_append, words_append]
  have e : words (bottom + BitVec.ofNat 64 (8 * P.length)) [c0, c1, c2, c3, c4, c5, c6, c7] =
      (words (bottom + BitVec.ofNat 64 (8 * P.length)) [c0, c1, c2, c3] **
       words (bottom + BitVec.ofNat 64 (8 * P.length) + 32) [c4, c5, c6, c7]) :=
    words_append _ [c0, c1, c2, c3] [c4, c5, c6, c7]
  rw [e]
  rfl

set_option maxRecDepth 100000

/-- RETURN with fewer than two operands. -/
theorem return_err_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_return.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 44 + signExtend21 0x0047f8#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hdepth : ¬ BitVec.slt ((0 : Word) + signExtend12 0x020#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom)) :
    cpsTripleWithin 31 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs ((0 : Word) + signExtend12 0x020#12)
        (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas) (base + 44 + 4) ((0 : Word) + signExtend12 0x002#12) g0 res fr) := by
  have h0 := ret_pro 0xff0#12 0x008#12 0x020#12 base L.sp L.ra (L.bottom + BitVec.ofNat 64 (32 * depth))
    L.bottom (L.codeBase + BitVec.ofNat 64 pc) scr.slot
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hbr := cpsBranchWithin_takenStripPure2
    (bge_spec_gen_within .x12 .x15 0x0018#13 ((0 : Word) + signExtend12 0x020#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom) (base + 16))
    (fun hp hq => hdepth (pure_end2 hp hq))
  have e1 : base + 16 + signExtend13 0x0018#13 = base + 40 := by rv64_addr
  rw [e1] at hbr
  have hli := li_a1 0x002#12 (base + 40) a1v
  have hj := jal_spec_within .x1 L.ra 0x0047f8#21 (base + 44) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 44 + 4)
    ((0 : Word) + signExtend12 0x002#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_return.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hbr := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_return.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hbr)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 40) Image.f_return.prog _ 10 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_return.prog 11 (base + 44) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hbr hli hj hx

/-- RETURN with two operands: status 0, the gas, and the limbs of the offset
    and size words in the context, at the `setjmp` return site. -/
theorem return_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base bI bM a1v g0 s2 st0 : Word) (res fr : List Word)
    (a b : Model.Word256) (rest : List Model.Word256) (gas pc : Nat)
    (hrep : Rep limbs (a :: b :: rest)) (hres : res.length = 8) (hfr : fr.length = 10)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_return.prog a = some i → cr a = some i)
    (hcI : ∀ a i, CodeReq.ofProg bI Image.f_return_impl.prog a = some i → cr a = some i)
    (hcM : ∀ a i, CodeReq.ofProg bM Image.f_memmove.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_bI : base + 36 + signExtend21 0x1fff68#21 = bI)
    (h_bM : bI + 88 + signExtend21 0x003860#21 = bM)
    (h_ra : (bI + 88 + 4 + signExtend12 0x000#12) &&& ~~~1 = bI + 92)
    (h_be : bI + 112 + signExtend21 0x004828#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (h_fb : E.fbase + 80 = E.slot2)
    (hbal : L.bottom.toNat % 8 = 0) (hcal : E.ctx.toNat % 8 = 0)
    (hord : L.bottom.toNat + 32 * 1025 ≤ E.ctx.toNat + 184)
    (hco : E.ctx.toNat + 248 ≤ 2 ^ 64)
    (hsv : ∀ i, i < 32 * 1025 → isValidByteAccess (L.bottom + BitVec.ofNat 64 i) = true)
    (hrv : ∀ i, i < 64 → isValidByteAccess (E.ctx + 184 + BitVec.ofNat 64 i) = true) :
    ∃ scr' j12 j13 j14 js2 fr',
      cpsTripleWithin 464 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
        (interp L scr limbs (rest.length + 2) gas pc ** exitFrame E a1v g0 s2 st0 res fr)
        (final L E scr' limbs j12 j13 j14 js2 ((0 : Word) + signExtend12 0x000#12)
          (BitVec.ofNat 64 gas) (limbsOf a ++ limbsOf b) fr') := by
  obtain ⟨o0, o1, o2, o3, z0, z1, z2, z3, rfl⟩ := list8 res hres
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩ := list10 fr hfr
  obtain ⟨hsplit, hPlen, hP⟩ := rep_split2 limbs a b rest hrep
  obtain ⟨a0, ha0⟩ : ∃ x, a.extractLsb' 0 64 = x := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ x, a.extractLsb' 64 64 = x := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ x, a.extractLsb' 128 64 = x := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ x, a.extractLsb' 192 64 = x := ⟨_, rfl⟩
  obtain ⟨b0, hb0⟩ : ∃ x, b.extractLsb' 0 64 = x := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ x, b.extractLsb' 64 64 = x := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ x, b.extractLsb' 128 64 = x := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ x, b.extractLsb' 192 64 = x := ⟨_, rfl⟩
  have hla : limbsOf a = [a0, a1, a2, a3] := by simp [limbsOf, ha0, ha1, ha2, ha3]
  have hlb : limbsOf b = [b0, b1, b2, b3] := by simp [limbsOf, hb0, hb1, hb2, hb3]
  have hlab : limbsOf b ++ limbsOf a = [b0, b1, b2, b3, a0, a1, a2, a3] := by rw [hla, hlb]; rfl
  rw [hlab] at hsplit
  obtain ⟨P, hPdef⟩ : ∃ P, limbs.take (4 * rest.length) = P := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, limbs.drop (4 * (rest.length + 2)) = Q := ⟨_, rfl⟩
  rw [hPdef] at hsplit hPlen hP
  rw [hQdef] at hsplit
  have hd := hrep.depth
  simp only [List.length_cons] at hd
  have hdepth := depth2_ok L.bottom rest.length (by omega)
  obtain ⟨X, hX⟩ : ∃ X, L.bottom + BitVec.ofNat 64 (8 * P.length) = X := ⟨_, rfl⟩
  have hX' : L.bottom + BitVec.ofNat 64 (8 * (4 * rest.length)) = X := by rw [← hX, hPlen]
  -- addresses: the machine stack
  have hL : L.sp = E.fbase + 104 := by
    apply addr_shift L.sp E.fbase (signExtend12 0xff0#12 + (signExtend12 0xff0#12 + signExtend12 0x008#12)) 80 104
    · rw [← BitVec.add_assoc, ← BitVec.add_assoc, h_slot2, h_fb]
    · decide
  have h_sp : L.sp + signExtend12 0xff0#12 + signExtend12 0xfb0#12 = E.fbase + 8 := by
    rw [hL]; exact addr3 _ _ _ _ _ (by decide)
  have h_f0 : E.fbase + 8 + signExtend12 0x000#12 = E.fbase + 8 := add_se0 _
  have h_f1 : E.fbase + 8 + signExtend12 0x008#12 = E.fbase + 16 := addr2 _ _ _ _ (by decide)
  have h_f3 : E.fbase + 8 + signExtend12 0x018#12 = E.fbase + 32 := addr2 _ _ _ _ (by decide)
  have h_f4 : E.fbase + 8 + signExtend12 0x020#12 = E.fbase + 40 := addr2 _ _ _ _ (by decide)
  have h_f5 : E.fbase + 8 + signExtend12 0x028#12 = E.fbase + 48 := addr2 _ _ _ _ (by decide)
  have h_f6 : E.fbase + 8 + signExtend12 0x030#12 = E.fbase + 56 := addr2 _ _ _ _ (by decide)
  have h_f7 : E.fbase + 8 + signExtend12 0x038#12 = E.fbase + 64 := addr2 _ _ _ _ (by decide)
  have h_f8 : E.fbase + 8 + signExtend12 0x040#12 = E.fbase + 72 := addr2 _ _ _ _ (by decide)
  have h_f9 : E.fbase + 8 + signExtend12 0x048#12 = E.slot2 := by
    rw [← h_fb]; exact addr2 _ _ _ _ (by decide)
  have h_scell : E.fbase + 8 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.fbase :=
    addr3_zero _ _ _ _ (by decide)
  -- addresses: the operand stack
  have h_src1 : (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfe0#12 = X + 32 := by
    rw [se_fe0, ← hX']; exact slot_addr L.bottom rest.length 32 32 (by omega) (by omega)
  have h_src2 : X + 32 + signExtend12 0xfe0#12 = X := addr2_zero _ _ _ (by decide)
  -- addresses: the context
  have h_dst1 : E.ctx + signExtend12 0x0b8#12 = E.ctx + 184 := by
    rw [show signExtend12 0x0b8#12 = (184 : Word) by decide]
  have h_dst2 : E.ctx + signExtend12 0x0d8#12 = E.ctx + 184 + 32 := by
    rw [BitVec.add_assoc, show (184 : Word) + 32 = signExtend12 0x0d8#12 by decide]
  have h_gcell : E.ctx + signExtend12 0x008#12 = E.ctx + 8 := by rw [se_lit_8]
  -- side conditions of the two copies
  have hXn : X.toNat = L.bottom.toNat + 8 * (4 * rest.length) := by
    rw [← hX']; exact toNat_add_ofNat' _ _ (by omega)
  have hX32 : (X + 32).toNat = X.toNat + 32 := toNat_add_ofNat' X 32 (by omega)
  have hD1 : (E.ctx + 184).toNat = E.ctx.toNat + 184 := toNat_add_ofNat' E.ctx 184 (by omega)
  have hD2 : (E.ctx + 184 + 32).toNat = E.ctx.toNat + 184 + 32 := by
    rw [← hD1]; exact toNat_add_ofNat' (E.ctx + 184) 32 (by omega)
  have hs1v : ∀ i, i < 32 → isValidByteAccess (X + 32 + BitVec.ofNat 64 i) = true := by
    intro i hi
    have e : X + 32 + BitVec.ofNat 64 i = L.bottom + BitVec.ofNat 64 (8 * (4 * rest.length) + 32 + i) := by
      rw [← hX']
      show L.bottom + BitVec.ofNat 64 (8 * (4 * rest.length)) + BitVec.ofNat 64 32 + BitVec.ofNat 64 i = _
      rw [ofNat_add_ofNat, ofNat_add_ofNat, Nat.add_assoc]
    rw [e]; exact hsv _ (by omega)
  have hs2v : ∀ i, i < 32 → isValidByteAccess (X + BitVec.ofNat 64 i) = true := by
    intro i hi
    rw [← hX', ofNat_add_ofNat]; exact hsv _ (by omega)
  have hd1v : ∀ i, i < 32 → isValidByteAccess (E.ctx + 184 + BitVec.ofNat 64 i) = true :=
    fun i hi => hrv i (by omega)
  have hd2v : ∀ i, i < 32 → isValidByteAccess (E.ctx + 184 + 32 + BitVec.ofNat 64 i) = true := by
    intro i hi
    show isValidByteAccess (E.ctx + 184 + BitVec.ofNat 64 32 + BitVec.ofNat 64 i) = true
    rw [ofNat_add_ofNat]; exact hrv _ (by omega)
  have hlt1 : BitVec.ult (X + 32) (E.ctx + 184) := by
    rw [BitVec.ult, hX32, hXn, hD1]; simp; omega
  have hlt2 : BitVec.ult X (E.ctx + 184 + 32) := by
    rw [BitVec.ult, hXn, hD2]; simp; omega
  -- the three pieces
  have h1 := return_spec base L.sp L.ra (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) L.bottom
    (L.codeBase + BitVec.ofNat 64 pc) scr.slot E.ctx a1v (BitVec.ofNat 64 gas) (frameSlot L.sp) rfl hdepth
  rw [h_bI] at h1
  have h2 := return_impl_spec cr bI bM (L.sp + signExtend12 0xff0#12) (base + 36 + 4)
    ((0 : Word) + signExtend12 0x000#12) E.ctx (L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2)))
    (BitVec.ofNat 64 gas) ((L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) - L.bottom)
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 (BitVec.ofNat 64 gas)
    a0 a1 a2 a3 b0 b1 b2 b3 o0 o1 o2 o3 z0 z1 z2 z3
    x1 x2 x4 x5 x6 x7 x8 x9 s2 g0
    (E.fbase + 8) (E.fbase + 8) (E.fbase + 16) (E.fbase + 32) (E.fbase + 40) (E.fbase + 48)
    (E.fbase + 56) (E.fbase + 64) (E.fbase + 72) E.slot2 (X + 32) X (E.ctx + 184) (E.ctx + 184 + 32)
    (E.ctx + 8) hcI hcM h_bM h_ra h_sp h_f0 h_f1 h_f3 h_f4 h_f5 h_f6 h_f7 h_f8 h_f9
    h_src1 h_src2 h_dst1 h_dst2 h_gcell
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hs1v hs2v hd1v hd2v hlt1 hlt2
  rw [h_be] at h2
  have h3 := exit_chain cr E.be E.bl E.ctx (E.fbase + 8) (bI + 112 + 4)
    ((0 : Word) + signExtend12 0x000#12) (E.ctx + 184 + 32 + BitVec.ofNat 64 0) E.jb x0 st0 E.fbase
    (X + signExtend12 0xfe0#12) (E.fbase + 8 + signExtend12 0x008#12 + signExtend12 0x008#12)
    ((L.bottom + BitVec.ofNat 64 (32 * (rest.length + 2))) + signExtend12 0xfa0#12) E.ctx
    ((0 : Word) + signExtend12 0x000#12) (BitVec.ofNat 64 gas)
    E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_scell
  have h1 := cpsTripleWithin_extend_code hc h1
  -- the regions, cell by cell
  have hw1 := words_mid44 L.bottom P Q b0 b1 b2 b3 a0 a1 a2 a3
  rw [← hsplit, hX] at hw1
  have hr1 : words (E.ctx + 184) [o0, o1, o2, o3, z0, z1, z2, z3] =
      (words (E.ctx + 184) [o0, o1, o2, o3] ** words (E.ctx + 184 + 32) [z0, z1, z2, z3]) :=
    words_append _ [o0, o1, o2, o3] [z0, z1, z2, z3]
  have hr2 : words (E.ctx + 184) (limbsOf a ++ limbsOf b) =
      (words (E.ctx + 184) [a0, a1, a2, a3] ** words (E.ctx + 184 + 32) [b0, b1, b2, b3]) := by
    rw [hla, hlb]; exact words_append _ [a0, a1, a2, a3] [b0, b1, b2, b3]
  refine ⟨{ scr with slot := L.ra }, BitVec.ofNat 64 0, BitVec.ofNat 64 gas,
    (extractByte b0 0).zeroExtend 64, base + 36 + 4,
    [bI + 112 + 4, E.ctx + 184, E.ctx + 184 + 32, x3, E.c5, E.c4, E.c3, E.c2, E.c1, E.c0], ?_⟩
  unfold interp exitFrame final
  rw [hw1, hr1, hr2, words_10 E.fbase x0 x1 x2 x3 x4 x5 x6 x7 x8 x9,
    words_10 E.fbase (bI + 112 + 4) (E.ctx + 184) (E.ctx + 184 + 32) x3 E.c5 E.c4 E.c3 E.c2 E.c1 E.c0]
  runBlock h1 h2 h3

end PureInterp.Machine
