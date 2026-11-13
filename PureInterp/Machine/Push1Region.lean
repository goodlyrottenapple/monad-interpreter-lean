import PureInterp.Machine.Lemmas
import PureInterp.Handlers.Push1

/-!
# Reading bytecode through the region, and PUSH1 over the region

`lbu_region` is a handler's `lbu k(a5)` stated against the whole bytecode
buffer, so a handler that reads several bytes needs no case split on which
doublewords they fall in. `push1_region` is the PUSH1 handler in that form.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

theorem lbu_region (rd : Reg) (codeBase vOld base : Word) (code : List (BitVec 8)) (pc k : Nat)
    (ok : BitVec 12) (hrd : rd ≠ .x0) (hok : signExtend12 ok = BitVec.ofNat 64 k)
    (hal : codeBase.toNat % 8 = 0) (hi : pc + k < code.length)
    (hover : codeBase.toNat + (pc + k) < 2 ^ 64)
    (hvalid : isValidByteAccess ((codeBase + BitVec.ofNat 64 pc) + signExtend12 ok) = true) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (.LBU rd .x15 ok))
      ((.x15 ↦ᵣ (codeBase + BitVec.ofNat 64 pc)) ** (rd ↦ᵣ vOld) ** bytesRegion codeBase code)
      ((.x15 ↦ᵣ (codeBase + BitVec.ofNat 64 pc)) ** (rd ↦ᵣ ((code[pc + k]).zeroExtend 64)) ** bytesRegion codeBase code) := by
  obtain ⟨cwAddr, cw, front, rest, hf, hr, heq, hcal, hcbyte⟩ :=
    code_cell codeBase code pc k ok hok hal hi hover
  have l := lbu_spec_gen_within rd .x15 (codeBase + BitVec.ofNat 64 pc) vOld ok base cwAddr cw hrd hcal hvalid
  rw [hcbyte] at l
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) l)

/-- Fall-through path of PUSH1, over the bytecode region. -/
theorem push1_region
    (base sp ra slot gas top bottom codeBase entryAddr h r16 r17 : Word)
    (code : List (BitVec 8)) (pc : Nat)
    (c0 c1 c2 c3 mslot t0 t1 t2 t3 tcell : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (h_t0 : top + signExtend12 0x000#12 = t0) (h_t1 : top + signExtend12 0x008#12 = t1)
    (h_t2 : top + signExtend12 0x010#12 = t2) (h_t3 : top + signExtend12 0x018#12 = t3)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffd#12) 0)
    (hroom : ¬ BitVec.slt ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (top - bottom))
    (hal : codeBase.toNat % 8 = 0) (hi : pc + 2 < code.length)
    (hover : codeBase.toNat + (pc + 2) < 2 ^ 64)
    (hvalid1 : isValidByteAccess ((codeBase + BitVec.ofNat 64 pc) + signExtend12 0x001#12) = true)
    (hvalid2 : isValidByteAccess ((codeBase + BitVec.ofNat 64 pc) + signExtend12 0x002#12) = true)
    (hent : base + (56 : Word) + (((0x1fffa#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0xd0c#12 + (((code[pc + 2]'(by omega)).zeroExtend 64) <<< (0x03#6).toNat) = entryAddr) :
    cpsTripleWithin 24 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_push_1.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ (codeBase + BitVec.ofNat 64 pc)) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) **
       (mslot ↦ₘ slot) ** (t0 ↦ₘ c0) ** (t1 ↦ₘ c1) ** (t2 ↦ₘ c2) ** (t3 ↦ₘ c3) **
       bytesRegion codeBase code ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) **
       (.x2 ↦ᵣ (sp + signExtend12 0xff0#12 + signExtend12 0x010#12)) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ (top + signExtend12 0x020#12)) **
       (.x14 ↦ᵣ (gas + signExtend12 0xffd#12)) ** (.x15 ↦ᵣ ((codeBase + BitVec.ofNat 64 pc) + signExtend12 0x002#12)) **
       (.x16 ↦ᵣ h) ** (.x17 ↦ᵣ (((code[pc + 2]'(by omega)).zeroExtend 64) <<< (0x03#6).toNat)) **
       (mslot ↦ₘ ra) ** (t0 ↦ₘ ((code[pc + 1]'(by omega)).zeroExtend 64)) ** (t1 ↦ₘ 0) ** (t2 ↦ₘ 0) ** (t3 ↦ₘ 0) **
       bytesRegion codeBase code ** (tcell ↦ₘ h)) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base sp ra slot gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0054#13 (gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have h1 := room 0x00008#20 0xfe0#12 (base + 16) top bottom r16 r17
  have hblt2 := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x17 .x16 0x004c#13 ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (top - bottom) (base + 28))
    (fun hp hq => hroom (pure_end2 hp hq))
  have hl1 := lbu_region .x16 codeBase (top - bottom) (base + 32) code pc 1 0x001#12
    (by decide) se_001 hal (by omega) (by omega) hvalid1
  have h2 := push_store 0x008#12 0x010#12 0x000#12 0x018#12 (base + 36) top ((code[pc + 1]'(by omega)).zeroExtend 64) c1 c2 c0 c3
  have hl2 := lbu_region .x17 codeBase ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (base + 52) code pc 2 0x002#12
    (by decide) se_002 hal hi hover hvalid2
  have h3 := dispatch_addr 0x008#12 0xd0c#12 0x1fffa#20 (base + 56) (sp + signExtend12 0xff0#12) ra
    ((code[pc + 1]'(by omega)).zeroExtend 64) ((code[pc + 2]'(by omega)).zeroExtend 64) ra
  rw [hent] at h3
  have h4 := dispatch_load 0x000#12 0x020#12 0x002#12 0x010#12 (base + 76) (codeBase + BitVec.ofNat 64 pc) top
    (sp + signExtend12 0xff0#12) entryAddr h
  have hj := jalr_x0_spec_gen_within .x16 h 0x000#12 (base + 92)
  rw [h_mslot] at h0 h3
  rw [h_t0, h_t1, h_t2, h_t3] at h2
  rw [h_tcell] at h4
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_push_1.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hblt := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_push_1.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) h1
  have hblt2 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 7 (base + 28) (by decide) (by decide) (by rfl))) hblt2
  have hl1 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 8 (base + 32) (by decide) (by decide) (by rfl))) hl1
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 36) Image.f_push_1.prog _ 9 (by rfl) (by decide) (by decide) (by decide)) h2
  have hl2 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 13 (base + 52) (by decide) (by decide) (by rfl))) hl2
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 56) Image.f_push_1.prog _ 14 (by rfl) (by decide) (by decide) (by decide)) h3
  have h4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 76) Image.f_push_1.prog _ 19 (by rfl) (by decide) (by decide) (by decide)) h4
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 23 (base + 92) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hblt h1 hblt2 hl1 h2 hl2 h3 h4 hj

end PureInterp.Machine
