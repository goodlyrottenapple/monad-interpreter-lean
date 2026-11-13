import PureInterp.Entry.Bytes

/-!
# `memcpy`

`cxx/platform.cpp`'s forward byte loop. Source: the range `[j0, j0 + n)` of an
aligned `bytesRegion sbase sbs`; destination: the range `[i0, i0 + n)` of a
separate aligned `bytesRegion dbase bs`, which afterwards holds
`splice bs i0 ((sbs.drop j0).take n)`.

The loop (`lbu; addi; addi; sb; bne`, 5 instructions per byte) is proved by
induction on the number of bytes still to copy, with the invariant "the first
`k` bytes are copied, `a1 = sbase + j0 + k`, `a5 = dbase + i0 + k`".
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem trunc_zext (b : BitVec 8) : ((b.zeroExtend 64 : Word).truncate 8) = b := by
  ext i; simp

theorem getD_of_lt (l : List (BitVec 8)) (i : Nat) (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem memcpy_head (oZ : BitVec 12) (base d s nW r15 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .ADD .x12 .x11 .x12, .ADDI .x15 .x10 oZ])
      ((.x10 ↦ᵣ d) ** (.x11 ↦ᵣ s) ** (.x12 ↦ᵣ nW) ** (.x15 ↦ᵣ r15))
      ((.x10 ↦ᵣ d) ** (.x11 ↦ᵣ s) ** (.x12 ↦ᵣ (s + nW)) ** (.x15 ↦ᵣ (d + signExtend12 oZ))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem memcpy_incs (o1 o2 : BitVec 12) (base p q : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .ADDI .x11 .x11 o1, .ADDI .x15 .x15 o2])
      ((.x11 ↦ᵣ p) ** (.x15 ↦ᵣ q))
      ((.x11 ↦ᵣ (p + signExtend12 o1)) ** (.x15 ↦ᵣ (q + signExtend12 o2))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- One more copied byte extends the copied prefix. -/
theorem splice_copy_step (bs sbs : List (BitVec 8)) (i0 j0 k : Nat)
    (hs : j0 + k < sbs.length) (hd : i0 + k < bs.length) :
    (splice bs i0 ((sbs.drop j0).take k)).set (i0 + k) (sbs.getD (j0 + k) 0)
      = splice bs i0 ((sbs.drop j0).take (k + 1)) := by
  have hl : ((sbs.drop j0).take k).length = k := by simp; omega
  have := splice_set bs i0 ((sbs.drop j0).take k) (sbs.getD (j0 + k) 0) (by omega)
  rw [hl] at this
  rw [this]
  congr 1
  rw [List.take_add_one, List.getElem?_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hs]
  rfl

/-- The loop, from its head `base + 12` to the `ret` at `base + 32`:
    `k` bytes copied, `r + 1` to go. -/
theorem memcpy_loop (base sbase dbase : Word) (sbs bs : List (BitVec 8)) (j0 i0 n : Nat)
    (salign : sbase.toNat % 8 = 0) (slen : j0 + n ≤ sbs.length)
    (sover : sbase.toNat + (j0 + n) < 2 ^ 64)
    (svalid : ∀ j, j0 ≤ j → j < j0 + n → isValidByteAccess (sbase + BitVec.ofNat 64 j) = true)
    (dalign : dbase.toNat % 8 = 0) (dlen : i0 + n ≤ bs.length)
    (dover : dbase.toNat + (i0 + n) < 2 ^ 64)
    (dvalid : ∀ i, i0 ≤ i → i < i0 + n → isValidByteAccess (dbase + BitVec.ofNat 64 i) = true) :
    ∀ (r k : Nat) (w : Word), k + r + 1 = n →
    cpsTripleWithin (5 * (r + 1)) (base + 12) (base + 32)
      (CodeReq.ofProg base Image.f_memcpy.prog)
      ((.x11 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + k))) **
       (.x12 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) ** (.x14 ↦ᵣ w) **
       (.x15 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + k))) ** bytesRegion sbase sbs **
       bytesRegion dbase (splice bs i0 ((sbs.drop j0).take k)))
      ((.x11 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) **
       (.x12 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) **
       (.x14 ↦ᵣ ((sbs.getD (j0 + n - 1) 0).zeroExtend 64)) **
       (.x15 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) ** bytesRegion sbase sbs **
       bytesRegion dbase (splice bs i0 ((sbs.drop j0).take n))) := by
  intro r
  induction r with
  | zero =>
    intro k w hk
    obtain rfl : n = k + 1 := by omega
    rw [show j0 + (k + 1) = j0 + k + 1 from rfl, show i0 + (k + 1) = i0 + k + 1 from rfl,
      show j0 + k + 1 - 1 = j0 + k from rfl]
    have hcl : (splice bs i0 ((sbs.drop j0).take k)).length = bs.length :=
      splice_length _ _ _ (by simp; omega)
    have hl := lbu_region_at .x14 .x11 sbase (sbase + BitVec.ofNat 64 (j0 + k)) w 0x000#12
      (base + 12) sbs (j0 + k) (by decide) (add_se12_zero _) salign (by omega) (by omega)
      (svalid _ (by omega) (by omega))
    rw [← getD_of_lt sbs (j0 + k) (by omega)] at hl
    have hinc := memcpy_incs 0x001#12 0x001#12 (base + 16)
      (sbase + BitVec.ofNat 64 (j0 + k)) (dbase + BitVec.ofNat 64 (i0 + k))
    rw [ptr_succ, ptr_succ] at hinc
    have hsb := sb_region_at .x15 .x14 dbase (dbase + BitVec.ofNat 64 (i0 + k + 1))
      ((sbs.getD (j0 + k) 0).zeroExtend 64) 0xfff#12
      (base + 24) (splice bs i0 ((sbs.drop j0).take k)) (i0 + k)
      (ptr_pred _ _) dalign (by omega) (by omega) (dvalid _ (by omega) (by omega))
    rw [trunc_zext, splice_copy_step bs sbs i0 j0 k (by omega) (by omega)] at hsb
    have hbne := cpsBranchWithin_ntakenStripPure2
      (bne_spec_gen_within .x11 .x12 0x1ff0#13 (sbase + BitVec.ofNat 64 (j0 + k + 1))
        (sbase + BitVec.ofNat 64 (j0 + k + 1)) (base + 28))
      (fun hp hq => (pure_end2 hp hq) rfl)
    have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hl
    have hinc := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mono_sub base (base + 16) Image.f_memcpy.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hinc
    have hsb := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hsb
    have hbne := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 7 (base + 28) (by decide) (by decide) (by rfl))) hbne
    runBlock hl hinc hsb hbne
  | succ r ih =>
    intro k w hk
    have hcl : (splice bs i0 ((sbs.drop j0).take k)).length = bs.length :=
      splice_length _ _ _ (by simp; omega)
    have hl := lbu_region_at .x14 .x11 sbase (sbase + BitVec.ofNat 64 (j0 + k)) w 0x000#12
      (base + 12) sbs (j0 + k) (by decide) (add_se12_zero _) salign (by omega) (by omega)
      (svalid _ (by omega) (by omega))
    rw [← getD_of_lt sbs (j0 + k) (by omega)] at hl
    have hinc := memcpy_incs 0x001#12 0x001#12 (base + 16)
      (sbase + BitVec.ofNat 64 (j0 + k)) (dbase + BitVec.ofNat 64 (i0 + k))
    rw [ptr_succ, ptr_succ] at hinc
    have hsb := sb_region_at .x15 .x14 dbase (dbase + BitVec.ofNat 64 (i0 + k + 1))
      ((sbs.getD (j0 + k) 0).zeroExtend 64) 0xfff#12
      (base + 24) (splice bs i0 ((sbs.drop j0).take k)) (i0 + k)
      (ptr_pred _ _) dalign (by omega) (by omega) (dvalid _ (by omega) (by omega))
    rw [trunc_zext, splice_copy_step bs sbs i0 j0 k (by omega) (by omega)] at hsb
    have hbne := cpsBranchWithin_takenStripPure2
      (bne_spec_gen_within .x11 .x12 0x1ff0#13 (sbase + BitVec.ofNat 64 (j0 + k + 1))
        (sbase + BitVec.ofNat 64 (j0 + n)) (base + 28))
      (fun hp hq => ptr_ne sbase (j0 + k + 1) (j0 + n) (by omega) (by omega) (by omega)
        (pure_end2 hp hq))
    have e : base + 28 + signExtend13 0x1ff0#13 = base + 12 := by rv64_addr
    rw [e] at hbne
    have ih' := ih (k + 1) ((sbs.getD (j0 + k) 0).zeroExtend 64) (by omega)
    rw [show j0 + (k + 1) = j0 + k + 1 from rfl, show i0 + (k + 1) = i0 + k + 1 from rfl] at ih'
    have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hl
    have hinc := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mono_sub base (base + 16) Image.f_memcpy.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hinc
    have hsb := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hsb
    have hbne := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 7 (base + 28) (by decide) (by decide) (by rfl))) hbne
    runBlock hl hinc hsb hbne ih'

/-- `memcpy(dbase + i0, sbase + j0, n)` with `n > 0`: the destination range
    receives the source range; `a0` (the destination) is preserved. -/
theorem memcpy_spec (base ra sbase dbase r14 r15 : Word) (sbs bs : List (BitVec 8))
    (j0 i0 n : Nat) (hn : 0 < n)
    (salign : sbase.toNat % 8 = 0) (slen : j0 + n ≤ sbs.length)
    (sover : sbase.toNat + (j0 + n) < 2 ^ 64)
    (svalid : ∀ j, j0 ≤ j → j < j0 + n → isValidByteAccess (sbase + BitVec.ofNat 64 j) = true)
    (dalign : dbase.toNat % 8 = 0) (dlen : i0 + n ≤ bs.length)
    (dover : dbase.toNat + (i0 + n) < 2 ^ 64)
    (dvalid : ∀ i, i0 ≤ i → i < i0 + n → isValidByteAccess (dbase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (5 * n + 4) base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_memcpy.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (dbase + BitVec.ofNat 64 i0)) **
       (.x11 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) ** (.x12 ↦ᵣ BitVec.ofNat 64 n) **
       (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) ** bytesRegion sbase sbs ** bytesRegion dbase bs)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (dbase + BitVec.ofNat 64 i0)) **
       (.x11 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) **
       (.x12 ↦ᵣ (sbase + BitVec.ofNat 64 (j0 + n))) **
       (.x14 ↦ᵣ ((sbs.getD (j0 + n - 1) 0).zeroExtend 64)) **
       (.x15 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) ** bytesRegion sbase sbs **
       bytesRegion dbase (splice bs i0 ((sbs.drop j0).take n))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : BitVec.ofNat 64 (m + 1) ≠ (0 : Word) := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    have : (m + 1) % 2 ^ 64 = 0 := this
    omega
  have hbeq := cpsBranchWithin_ntakenStripPure2
    (beq_spec_gen_within .x12 .x0 0x0020#13 (BitVec.ofNat 64 (m + 1)) 0 base)
    (fun hp hq => hne (pure_end2 hp hq))
  have h0 := memcpy_head 0x000#12 (base + 4) (dbase + BitVec.ofNat 64 i0)
    (sbase + BitVec.ofNat 64 j0) (BitVec.ofNat 64 (m + 1)) r15
  rw [add_se12_zero, ptr_add] at h0
  have hl := memcpy_loop base sbase dbase sbs bs j0 i0 (m + 1) salign slen sover svalid
    dalign dlen dover dvalid m 0 r14 (by omega)
  simp only [Nat.add_zero, List.take_zero, splice_nil] at hl
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 32)
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 0 base (by decide) (by decide) (by simp))) hbeq
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 4) Image.f_memcpy.prog _ 1 (by rfl) (by decide) (by decide) (by decide)) h0
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 8 (base + 32) (by decide) (by decide) (by rfl))) hj
  runBlock hbeq h0 hl hj

/-- `memcpy(d, s, 0)`: returns immediately. -/
theorem memcpy_zero (base ra nW : Word) (hn : nW = 0) :
    cpsTripleWithin 2 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_memcpy.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x12 ↦ᵣ nW))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x12 ↦ᵣ nW)) := by
  have hbeq := cpsBranchWithin_takenStripPure2
    (beq_spec_gen_within .x12 .x0 0x0020#13 nW 0 base)
    (fun hp hq => (pure_end2 hp hq) hn)
  have e : base + signExtend13 0x0020#13 = base + 32 := by
    rw [show signExtend13 0x0020#13 = (32 : Word) from by decide]
  rw [e] at hbeq
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 32)
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 0 base (by decide) (by decide) (by simp))) hbeq
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memcpy.prog 8 (base + 32) (by decide) (by decide) (by rfl))) hj
  runBlock hbeq hj

end PureInterp.Entry
