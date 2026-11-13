import PureInterp.Entry.Bytes

/-!
# `memset`

`cxx/platform.cpp`'s byte loop. The destination is the range `[i0, i0 + n)`
of an aligned `bytesRegion dbase bs`; afterwards the region holds
`splice bs i0 (replicate n b)` with `b` the low byte of the value argument.

The loop (`sb; addi; bne`, 3 instructions per byte) is proved by induction on
the number of bytes still to write, with the invariant "the first `k` bytes of
the range are written, `a5 = dbase + i0 + k`".
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem inc15 (o : BitVec 12) (base p : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x15 .x15 o])
      (.x15 ↦ᵣ p) (.x15 ↦ᵣ (p + signExtend12 o)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem memset_head (oZ : BitVec 12) (base d nW r14 r15 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .ADDI .x15 .x10 oZ, .ADD .x14 .x10 .x12])
      ((.x10 ↦ᵣ d) ** (.x12 ↦ᵣ nW) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15))
      ((.x10 ↦ᵣ d) ** (.x12 ↦ᵣ nW) ** (.x14 ↦ᵣ (d + nW)) ** (.x15 ↦ᵣ (d + signExtend12 oZ))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The loop, from its head `base + 12` to the `ret` at `base + 24`:
    `k` bytes written, `r + 1` to go. -/
theorem memset_loop (base dbase v : Word) (bs : List (BitVec 8)) (i0 n : Nat)
    (halign : dbase.toNat % 8 = 0) (hlen : i0 + n ≤ bs.length)
    (hover : dbase.toNat + (i0 + n) < 2 ^ 64)
    (hvalid : ∀ i, i0 ≤ i → i < i0 + n → isValidByteAccess (dbase + BitVec.ofNat 64 i) = true) :
    ∀ (r k : Nat), k + r + 1 = n →
    cpsTripleWithin (3 * (r + 1)) (base + 12) (base + 24)
      (CodeReq.ofProg base Image.f_memset.prog)
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) **
       (.x15 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + k))) **
       bytesRegion dbase (splice bs i0 (List.replicate k (v.truncate 8))))
      ((.x11 ↦ᵣ v) ** (.x14 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) **
       (.x15 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) **
       bytesRegion dbase (splice bs i0 (List.replicate n (v.truncate 8)))) := by
  intro r
  induction r with
  | zero =>
    intro k hk
    obtain rfl : n = k + 1 := by omega
    rw [show i0 + (k + 1) = i0 + k + 1 from rfl]
    have hcl : (splice bs i0 (List.replicate k (v.truncate 8))).length = bs.length :=
      splice_length _ _ _ (by simp; omega)
    have hsb := sb_region_at .x15 .x11 dbase (dbase + BitVec.ofNat 64 (i0 + k)) v 0x000#12
      (base + 12) (splice bs i0 (List.replicate k (v.truncate 8))) (i0 + k)
      (add_se12_zero _) halign (by omega) (by omega) (hvalid _ (by omega) (by omega))
    have hset : (splice bs i0 (List.replicate k (v.truncate 8))).set (i0 + k) (v.truncate 8)
        = splice bs i0 (List.replicate (k + 1) (v.truncate 8)) := by
      have := splice_set bs i0 (List.replicate k (v.truncate 8)) (v.truncate 8) (by simp; omega)
      rw [List.length_replicate] at this
      rw [this, ← List.replicate_succ']
    rw [hset] at hsb
    have hadd := inc15 0x001#12 (base + 16) (dbase + BitVec.ofNat 64 (i0 + k))
    rw [ptr_succ] at hadd
    have hbne := cpsBranchWithin_ntakenStripPure2
      (bne_spec_gen_within .x15 .x14 0x1ff8#13 (dbase + BitVec.ofNat 64 (i0 + k + 1))
        (dbase + BitVec.ofNat 64 (i0 + k + 1)) (base + 20))
      (fun hp hq => (pure_end2 hp hq) rfl)
    have hsb := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hsb
    have hadd := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mono_sub base (base + 16) Image.f_memset.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hadd
    have hbne := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 5 (base + 20) (by decide) (by decide) (by rfl))) hbne
    runBlock hsb hadd hbne
  | succ r ih =>
    intro k hk
    have hcl : (splice bs i0 (List.replicate k (v.truncate 8))).length = bs.length :=
      splice_length _ _ _ (by simp; omega)
    have hsb := sb_region_at .x15 .x11 dbase (dbase + BitVec.ofNat 64 (i0 + k)) v 0x000#12
      (base + 12) (splice bs i0 (List.replicate k (v.truncate 8))) (i0 + k)
      (add_se12_zero _) halign (by omega) (by omega) (hvalid _ (by omega) (by omega))
    have hset : (splice bs i0 (List.replicate k (v.truncate 8))).set (i0 + k) (v.truncate 8)
        = splice bs i0 (List.replicate (k + 1) (v.truncate 8)) := by
      have := splice_set bs i0 (List.replicate k (v.truncate 8)) (v.truncate 8) (by simp; omega)
      rw [List.length_replicate] at this
      rw [this, ← List.replicate_succ']
    rw [hset] at hsb
    have hadd := inc15 0x001#12 (base + 16) (dbase + BitVec.ofNat 64 (i0 + k))
    rw [ptr_succ] at hadd
    have hbne := cpsBranchWithin_takenStripPure2
      (bne_spec_gen_within .x15 .x14 0x1ff8#13 (dbase + BitVec.ofNat 64 (i0 + k + 1))
        (dbase + BitVec.ofNat 64 (i0 + n)) (base + 20))
      (fun hp hq => ptr_ne dbase (i0 + k + 1) (i0 + n) (by omega) (by omega) (by omega)
        (pure_end2 hp hq))
    have e : base + 20 + signExtend13 0x1ff8#13 = base + 12 := by rv64_addr
    rw [e] at hbne
    have ih' := ih (k + 1) (by omega)
    rw [show i0 + (k + 1) = i0 + k + 1 from rfl] at ih'
    have hsb := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hsb
    have hadd := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mono_sub base (base + 16) Image.f_memset.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hadd
    have hbne := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 5 (base + 20) (by decide) (by decide) (by rfl))) hbne
    runBlock hsb hadd hbne ih'

/-- `memset(dbase + i0, v, n)`: the range `[i0, i0 + n)` of the region is
    overwritten with the low byte of `v`; returns the destination in `a0`. -/
theorem memset_spec (base ra dbase v r14 r15 : Word) (bs : List (BitVec 8)) (i0 n : Nat)
    (halign : dbase.toNat % 8 = 0) (hlen : i0 + n ≤ bs.length)
    (hover : dbase.toNat + (i0 + n) < 2 ^ 64)
    (hvalid : ∀ i, i0 ≤ i → i < i0 + n → isValidByteAccess (dbase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (3 * n + 4) base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_memset.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (dbase + BitVec.ofNat 64 i0)) ** (.x11 ↦ᵣ v) **
       (.x12 ↦ᵣ BitVec.ofNat 64 n) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) ** bytesRegion dbase bs)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (dbase + BitVec.ofNat 64 i0)) ** (.x11 ↦ᵣ v) **
       (.x12 ↦ᵣ BitVec.ofNat 64 n) ** (.x14 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) **
       (.x15 ↦ᵣ (dbase + BitVec.ofNat 64 (i0 + n))) **
       bytesRegion dbase (splice bs i0 (List.replicate n (v.truncate 8)))) := by
  have h0 := memset_head 0x000#12 base (dbase + BitVec.ofNat 64 i0) (BitVec.ofNat 64 n) r14 r15
  rw [add_se12_zero, ptr_add] at h0
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 24)
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_memset.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hj
  cases n with
  | zero =>
    have hbeq := cpsBranchWithin_takenStripPure2
      (beq_spec_gen_within .x12 .x0 0x0010#13 (BitVec.ofNat 64 0) 0 (base + 8))
      (fun hp hq => (pure_end2 hp hq) rfl)
    have e : base + 8 + signExtend13 0x0010#13 = base + 24 := by rv64_addr
    rw [e] at hbeq
    have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 2 (base + 8) (by decide) (by decide) (by rfl))) hbeq
    simp only [Nat.add_zero, List.replicate_zero, splice_nil] at h0 ⊢
    runBlock h0 hbeq hj
  | succ m =>
    have hne : BitVec.ofNat 64 (m + 1) ≠ (0 : Word) := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      have : (m + 1) % 2 ^ 64 = 0 := this
      omega
    have hbeq := cpsBranchWithin_ntakenStripPure2
      (beq_spec_gen_within .x12 .x0 0x0010#13 (BitVec.ofNat 64 (m + 1)) 0 (base + 8))
      (fun hp hq => hne (pure_end2 hp hq))
    have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr base Image.f_memset.prog 2 (base + 8) (by decide) (by decide) (by rfl))) hbeq
    have hl := memset_loop base dbase v bs i0 (m + 1) halign hlen hover hvalid m 0 (by omega)
    simp only [Nat.add_zero, List.replicate_zero, splice_nil] at hl
    runBlock h0 hbeq hl hj

end PureInterp.Entry
