import PureInterp.Entry.Pad

/-!
# The `Intercode` constructor

`Intercode::Intercode(std::span<uint8_t const> code)` (the copy at
`0x8000a2e0`): `padded_code_ = pad(code)`, `code_size_ = code.size()`
(a 32-bit store at `this + 8`), then `jumpdest_map_ = find_jumpdests(code)`
constructed in place at `this + 16`.

`find_jumpdests` (121 instructions: allocation of the bitmap, a `memset`, the
scanning loop with its PUSH-skip, 16 byte stores assembling the vector
header) is NOT proved. `ctor_spec` takes its contract as the hypothesis
`hfj`: from the exact machine state at its call (everything the constructor
and `pad` leave, plus any extra resources `X` it needs) it returns to the
call site with `ra`-slot, `s0`-slot, `sp` and `s0` intact and some
postcondition `Q`. Everything else in the constructor is proved, including
the whole of `pad`.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-- The allocator's result is 32-byte aligned, hence doubleword aligned. -/
theorem round32_mod32 (hn : Word) : (round32 hn).toNat % 32 = 0 := by
  have h : round32 hn &&& 31#64 = 0 := by
    unfold round32
    rw [BitVec.and_assoc, show signExtend12 0xfe0#12 &&& 31#64 = 0 from by decide]
    simp
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at h2
  have e : (31#64 : Word).toNat = 2 ^ 5 - 1 := by decide
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at h2
  simpa using h2

theorem round32_aligned (hn : Word) : (round32 hn).toNat % 8 = 0 := by
  have := round32_mod32 hn
  omega

theorem ctor_prologue (oF o1 o2 o3 o4 oA oB oC : BitVec 12)
    (base sp ra s0 this cp nW a b c d : Word) :
    cpsTripleWithin 8 base (base + 32) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .SD .x2 .x8 o1, .SD .x2 .x11 o2, .ADDI .x8 .x10 oA, .ADDI .x10 .x11 oB,
      .ADDI .x11 .x12 oC, .SD .x2 .x1 o3, .SD .x2 .x12 o4])
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x10 ↦ᵣ this) ** (.x11 ↦ᵣ cp) **
       (.x12 ↦ᵣ nW) **
       ((sp + signExtend12 oF + signExtend12 o1) ↦ₘ a) **
       ((sp + signExtend12 oF + signExtend12 o2) ↦ₘ b) **
       ((sp + signExtend12 oF + signExtend12 o3) ↦ₘ c) **
       ((sp + signExtend12 oF + signExtend12 o4) ↦ₘ d))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) ** (.x8 ↦ᵣ (this + signExtend12 oA)) **
       (.x10 ↦ᵣ (cp + signExtend12 oB)) ** (.x11 ↦ᵣ (nW + signExtend12 oC)) ** (.x12 ↦ᵣ nW) **
       ((sp + signExtend12 oF + signExtend12 o1) ↦ₘ s0) **
       ((sp + signExtend12 oF + signExtend12 o2) ↦ₘ cp) **
       ((sp + signExtend12 oF + signExtend12 o3) ↦ₘ ra) **
       ((sp + signExtend12 oF + signExtend12 o4) ↦ₘ nW)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ctor_fields (o4 o2 oP : BitVec 12) (base spf this v r11 r12 nW cp f0 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .LD .x12 .x2 o4, .LD .x11 .x2 o2, .SD .x8 .x10 oP])
      ((.x2 ↦ᵣ spf) ** (.x8 ↦ᵣ this) ** (.x10 ↦ᵣ v) ** (.x11 ↦ᵣ r11) ** (.x12 ↦ᵣ r12) **
       ((spf + signExtend12 o4) ↦ₘ nW) ** ((spf + signExtend12 o2) ↦ₘ cp) **
       ((this + signExtend12 oP) ↦ₘ f0))
      ((.x2 ↦ᵣ spf) ** (.x8 ↦ᵣ this) ** (.x10 ↦ᵣ v) ** (.x11 ↦ᵣ cp) ** (.x12 ↦ᵣ nW) **
       ((spf + signExtend12 o4) ↦ₘ nW) ** ((spf + signExtend12 o2) ↦ₘ cp) **
       ((this + signExtend12 oP) ↦ₘ v)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ctor_arg (o : BitVec 12) (base this r10 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x10 .x8 o])
      ((.x8 ↦ᵣ this) ** (.x10 ↦ᵣ r10))
      ((.x8 ↦ᵣ this) ** (.x10 ↦ᵣ (this + signExtend12 o))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ctor_epilogue (o3 o1 oF : BitVec 12) (base spf r1 r8 ra s0 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .LD .x1 .x2 o3, .LD .x8 .x2 o1, .ADDI .x2 .x2 oF])
      ((.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ spf) ** (.x8 ↦ᵣ r8) **
       ((spf + signExtend12 o3) ↦ₘ ra) ** ((spf + signExtend12 o1) ↦ₘ s0))
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (spf + signExtend12 oF)) ** (.x8 ↦ᵣ s0) **
       ((spf + signExtend12 o3) ↦ₘ ra) ** ((spf + signExtend12 o1) ↦ₘ s0)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The constructor, given a contract `hfj` for `find_jumpdests`.
    `this` is the object, `spf = sp - 32` the constructor's frame; the code is
    the range `[j0, j0 + n)` of `sbs`; `buf` the fresh padded buffer. On
    return `this->padded_code_ = buf + 30`, the 32-bit `code_size_` holds `n`,
    the buffer holds `zeros(30) ++ code ++ zeros(33)`, and `Q` holds. -/
theorem ctor_spec (cr : CodeReq) (X Q : Assertion) [Assertion.PCFree X] [Assertion.PCFree Q]
    (nfj : Nat) (bi bp bn bm bc bf sp spf ra s0 s1 s2 s3 this sbase r14 r15 r1' : Word)
    (a b c d f0 f1 : Word) (rslot s0slot dslot nslot t0 t8 : Word)
    (m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf : Word) (c38 c30 c28 c20 c18 c00 c08 : Word)
    (sbs bs0 : List (BitVec 8)) (j0 n : Nat)
    (hci : ∀ a i, CodeReq.ofProg bi Image.f_Intercode_Intercode_8000a2e0.prog a = some i → cr a = some i)
    (hcp : ∀ a i, CodeReq.ofProg bp Image.f_Intercode_pad.prog a = some i → cr a = some i)
    (hcn : ∀ a i, CodeReq.ofProg bn Image.f_new_80009fb4.prog a = some i → cr a = some i)
    (hcm : ∀ a i, CodeReq.ofProg bm Image.f_memset.prog a = some i → cr a = some i)
    (hcc : ∀ a i, CodeReq.ofProg bc Image.f_memcpy.prog a = some i → cr a = some i)
    (h_bn : bp + 52 + signExtend21 0x1fff30#21 = bn)
    (h_bm : bp + 72 + signExtend21 0x1ffcec#21 = bm)
    (h_bc : bp + 96 + signExtend21 0x1ffc60#21 = bc)
    (h_bm2 : bp + 116 + signExtend21 0x1ffcc0#21 = bm)
    (h_r1 : (bp + 52 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 56)
    (h_r2 : (bp + 72 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 76)
    (h_r3 : (bp + 96 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 100)
    (h_r4 : (bp + 116 + 4 + signExtend12 0x000#12) &&& ~~~1 = bp + 120)
    (h_c38 : spf + signExtend12 0xfc0#12 + signExtend12 0x038#12 = c38)
    (h_c30 : spf + signExtend12 0xfc0#12 + signExtend12 0x030#12 = c30)
    (h_c28 : spf + signExtend12 0xfc0#12 + signExtend12 0x028#12 = c28)
    (h_c20 : spf + signExtend12 0xfc0#12 + signExtend12 0x020#12 = c20)
    (h_c18 : spf + signExtend12 0xfc0#12 + signExtend12 0x018#12 = c18)
    (h_c00 : spf + signExtend12 0xfc0#12 + signExtend12 0x000#12 = c00)
    (h_c08 : spf + signExtend12 0xfc0#12 + signExtend12 0x008#12 = c08)
    (h_hcell1 : pcrel (bn + 4) 0x1fff7#20 0x9a8#12 = hcell)
    (h_hend : pcrel (bn + 12) 0x23ff7#20 0x9c0#12 = hend)
    (h_hcell3 : pcrel (bn + 48 + 4) 0x1fff7#20 0x978#12 = hcell)
    (h_buf : round32 hn = buf)
    (hsize : n < 2 ^ 20)
    (hfit : ¬ BitVec.ult (hend - round32 hn) (BitVec.ofNat 64 n + signExtend12 0x03f#12))
    (salign : sbase.toNat % 8 = 0) (slen : j0 + n ≤ sbs.length)
    (sover : sbase.toNat + (j0 + n) < 2 ^ 64)
    (svalid : ∀ j, j0 ≤ j → j < j0 + n → isValidByteAccess (sbase + BitVec.ofNat 64 j) = true)
    (hlen : bs0.length = n + 63)
    (hover : buf.toNat + (n + 63) < 2 ^ 64)
    (hvalid : ∀ i, i < n + 63 → isValidByteAccess (buf + BitVec.ofNat 64 i) = true)
    (h_spf : sp + signExtend12 0xfe0#12 = spf)
    (h_sp : spf + signExtend12 0x020#12 = sp)
    (h_bp : bi + 32 + signExtend21 0x1ffd50#21 = bp)
    (h_bf : bi + 56 + signExtend21 0x1ffde4#21 = bf)
    (h_ri1 : (bi + 32 + 4 + signExtend12 0x000#12) &&& ~~~1 = bi + 36)
    (h_s0slot : spf + signExtend12 0x010#12 = s0slot)
    (h_dslot : spf + signExtend12 0x000#12 = dslot)
    (h_rslot : spf + signExtend12 0x018#12 = rslot)
    (h_nslot : spf + signExtend12 0x008#12 = nslot)
    (h_t0 : this + signExtend12 0x000#12 = t0)
    (h_t8 : alignToDword (this + signExtend12 0x008#12) = t8)
    (h_t8v : isValidMemAccess (this + signExtend12 0x008#12) = true)
    (hfj : cpsTripleWithin nfj bf (bi + 60) cr
      ((.x1 ↦ᵣ (bi + 56 + 4)) ** (.x2 ↦ᵣ spf) ** (.x8 ↦ᵣ this) **
       (.x10 ↦ᵣ (this + signExtend12 0x010#12)) ** (.x11 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) ** (.x12 ↦ᵣ (BitVec.ofNat 64 n)) **
       (rslot ↦ₘ ra) ** (s0slot ↦ₘ s0) **
       (.x0 ↦ᵣ 0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
       (.x14 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n + 33))) **
       (.x15 ↦ᵣ (buf + BitVec.ofNat 64 (30 + n + 33))) **
       (c38 ↦ₘ (bi + 32 + 4)) ** (c30 ↦ₘ this) ** (c28 ↦ₘ s1) ** (c20 ↦ₘ s2) ** (c18 ↦ₘ s3) **
       (c00 ↦ₘ (sbase + BitVec.ofNat 64 j0)) ** (c08 ↦ₘ (BitVec.ofNat 64 n)) **
       (hcell ↦ₘ (BitVec.ofNat 64 n + signExtend12 0x03f#12 + buf)) **
       (dslot ↦ₘ (sbase + BitVec.ofNat 64 j0)) ** (nslot ↦ₘ (BitVec.ofNat 64 n)) **
       (t0 ↦ₘ (buf + BitVec.ofNat 64 30)) ** (t8 ↦ₘ (replaceWord32 f1 ((byteOffset (this + signExtend12 0x008#12)) / 4) ((BitVec.ofNat 64 n).truncate 32))) **
       bytesRegion sbase sbs ** bytesRegion buf (List.replicate 30 0 ++ (sbs.drop j0).take n ++ List.replicate 33 0) ** X)
      ((.x1 ↦ᵣ r1') ** (.x2 ↦ᵣ spf) ** (.x8 ↦ᵣ this) ** (rslot ↦ₘ ra) ** (s0slot ↦ₘ s0) ** Q)) :
    cpsTripleWithin (5 * n + nfj + 272) bi ((ra + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
       (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x10 ↦ᵣ this) ** (.x11 ↦ᵣ (sbase + BitVec.ofNat 64 j0)) **
       (.x12 ↦ᵣ (BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (s0slot ↦ₘ a) ** (dslot ↦ₘ b) ** (rslot ↦ₘ c) ** (nslot ↦ₘ d) **
       (t0 ↦ₘ f0) ** (t8 ↦ₘ f1) **
       (c38 ↦ₘ m0) ** (c30 ↦ₘ m1) ** (c28 ↦ₘ m2) ** (c20 ↦ₘ m3) ** (c18 ↦ₘ m4) **
       (c00 ↦ₘ m5) ** (c08 ↦ₘ m6) ** (hcell ↦ₘ hn) ** bytesRegion sbase sbs **
       bytesRegion buf bs0 ** X)
      ((.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ s0) ** (rslot ↦ₘ ra) ** (s0slot ↦ₘ s0) ** Q) := by
  subst h_spf
  have h0 := ctor_prologue 0xfe0#12 0x010#12 0x000#12 0x018#12 0x008#12 0x000#12 0x000#12 0x000#12
    bi sp ra s0 this (sbase + BitVec.ofNat 64 j0) (BitVec.ofNat 64 n) a b c d
  rw [h_s0slot, h_dslot, h_rslot, h_nslot] at h0
  simp only [add_se12_zero] at h0
  generalize sp + signExtend12 0xfe0#12 = spf at *
  have hj1 := jal_spec_within .x1 ra 0x1ffd50#21 (bi + 32) (by decide)
  rw [h_bp] at hj1
  have hp := pad_spec cr bp bn bm bc spf (bi + 32 + 4) this s1 s2 s3 sbase (BitVec.ofNat 64 n) r14 r15
    m0 m1 m2 m3 m4 m5 m6 hn hcell hend buf c38 c30 c28 c20 c18 c00 c08 sbs bs0 j0 n
    hcp hcn hcm hcc h_bn h_bm h_bc h_bm2 h_r1 h_r2 h_r3 h_r4 h_c38 h_c30 h_c28 h_c20 h_c18 h_c00 h_c08 h_hcell1 h_hend h_hcell3 h_buf hsize hfit salign slen sover svalid (h_buf ▸ round32_aligned hn) hlen hover hvalid
  rw [h_ri1] at hp
  have h1 := ctor_fields 0x008#12 0x000#12 0x000#12 (bi + 36) spf this (buf + BitVec.ofNat 64 30)
    0 (BitVec.ofNat 64 33) (BitVec.ofNat 64 n) (sbase + BitVec.ofNat 64 j0) f0
  rw [h_nslot, h_dslot, h_t0] at h1
  have hsw := sw_spec_gen_within .x8 .x12 this (BitVec.ofNat 64 n) 0x008#12 (bi + 48) t8 f1 h_t8 h_t8v
  have h2 := ctor_arg 0x010#12 (bi + 52) this (buf + BitVec.ofNat 64 30)
  have hj2 := jal_spec_within .x1 (bi + 32 + 4) 0x1ffde4#21 (bi + 56) (by decide)
  rw [h_bf] at hj2
  have h3 := ctor_epilogue 0x018#12 0x010#12 0x020#12 (bi + 60) spf r1' this ra s0
  rw [h_rslot, h_s0slot, h_sp] at h3
  have hr := jalr_x0_spec_gen_within .x1 ra 0x000#12 (bi + 72)
  have h0 := cpsTripleWithin_extend_code (fun a i h => hci a i
    (CodeReq.ofProg_mono_sub bi bi Image.f_Intercode_Intercode_8000a2e0.prog _ 0 (by simp) (by decide) (by decide) (by decide) a i h)) h0
  have hj1 := cpsTripleWithin_extend_code (fun a i h => hci a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bi Image.f_Intercode_Intercode_8000a2e0.prog 8 (bi + 32) (by decide) (by decide) (by rfl)) a i h)) hj1
  have h1 := cpsTripleWithin_extend_code (fun a i h => hci a i
    (CodeReq.ofProg_mono_sub bi (bi + 36) Image.f_Intercode_Intercode_8000a2e0.prog _ 9 (by rfl) (by decide) (by decide) (by decide) a i h)) h1
  have hsw := cpsTripleWithin_extend_code (fun a i h => hci a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bi Image.f_Intercode_Intercode_8000a2e0.prog 12 (bi + 48) (by decide) (by decide) (by rfl)) a i h)) hsw
  have h2 := cpsTripleWithin_extend_code (fun a i h => hci a i
    (CodeReq.ofProg_mono_sub bi (bi + 52) Image.f_Intercode_Intercode_8000a2e0.prog _ 13 (by rfl) (by decide) (by decide) (by decide) a i h)) h2
  have hj2 := cpsTripleWithin_extend_code (fun a i h => hci a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bi Image.f_Intercode_Intercode_8000a2e0.prog 14 (bi + 56) (by decide) (by decide) (by rfl)) a i h)) hj2
  have h3 := cpsTripleWithin_extend_code (fun a i h => hci a i
    (CodeReq.ofProg_mono_sub bi (bi + 60) Image.f_Intercode_Intercode_8000a2e0.prog _ 15 (by rfl) (by decide) (by decide) (by decide) a i h)) h3
  have hr := cpsTripleWithin_extend_code (fun a i h => hci a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bi Image.f_Intercode_Intercode_8000a2e0.prog 18 (bi + 72) (by decide) (by decide) (by rfl)) a i h)) hr
  runBlock h0 hj1 hp h1 hsw h2 hj2 hfj h3 hr

end PureInterp.Entry
