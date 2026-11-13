import PureInterp.Handlers.Add

/-!
# The POP handler

`f_pop`, 21 instructions. Fall-through path: at least 2 gas and one operand.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem pop_spec
    (base sp ra slot gas top bottom ip cw cwAddr entryAddr h r16 r17 mslot tcell : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffe#12) 0)
    (hdepth : BitVec.slt (0 : Word) (top - bottom))
    (halign : alignToDword (ip + signExtend12 0x001#12) = cwAddr)
    (hvalid : isValidByteAccess (ip + signExtend12 0x001#12) = true)
    (hent : base + (28 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0xca8#12 +
        (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat) =
        entryAddr) :
    cpsTripleWithin 17 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_pop.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) **
       (mslot ↦ₘ slot) ** (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) **
       (.x2 ↦ᵣ (sp + signExtend12 0xff0#12 + signExtend12 0x010#12)) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ (top + signExtend12 0xfe0#12)) **
       (.x14 ↦ᵣ (gas + signExtend12 0xffe#12)) ** (.x15 ↦ᵣ (ip + signExtend12 0x001#12)) **
       (.x16 ↦ᵣ h) **
       (.x17 ↦ᵣ (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<<
          (0x03#6).toNat)) **
       (mslot ↦ₘ ra) ** (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h)) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffe#12 base sp ra slot gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0038#13 (gas + signExtend12 0xffe#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have hs := sub_spec_gen_within .x16 .x13 .x12 top bottom r16 (base + 16) (by decide)
  have hbge := cpsBranchWithin_ntakenStripPure2
    (bge_spec_gen_within .x0 .x16 0x0038#13 (0 : Word) (top - bottom) (base + 20))
    (fun hp hq => (pure_end2 hp hq) hdepth)
  have hl := lbu_spec_gen_within .x17 .x15 ip r17 0x001#12 (base + 24) cwAddr cw
    (by decide) halign hvalid
  have h3 := dispatch_addr 0x008#12 0xca8#12 0x20000#20 (base + 28) (sp + signExtend12 0xff0#12) ra
    (top - bottom) ((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) ra
  rw [hent] at h3
  have h4 := dispatch_load 0x000#12 0xfe0#12 0x001#12 0x010#12 (base + 48) ip top
    (sp + signExtend12 0xff0#12) entryAddr h
  have hj := jalr_x0_spec_gen_within .x16 h 0x000#12 (base + 64)
  rw [h_mslot] at h0 h3
  rw [h_tcell] at h4
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_pop.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hblt := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt
  have hs := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hs
  have hbge := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 5 (base + 20) (by decide) (by decide) (by rfl))) hbge
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hl
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 28) Image.f_pop.prog _ 7 (by rfl) (by decide) (by decide) (by decide)) h3
  have h4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 48) Image.f_pop.prog _ 12 (by rfl) (by decide) (by decide) (by decide)) h4
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 16 (base + 64) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hblt hs hbge hl h3 h4 hj

end PureInterp.Handlers
