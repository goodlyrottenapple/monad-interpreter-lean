import PureInterp.Handlers.Add

/-!
# The SWAP1 handler

`f_swap_1`, 37 instructions. Fall-through path: at least 3 gas and two
operands; the top two stack words are exchanged limb by limb.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem depth_swap (o32 : BitVec 12) (base top bottom r17 r6 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .SUB .x17 .x13 .x12, .ADDI .x6 .x0 o32])
      ((.x0 ↦ᵣ 0) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) ** (.x17 ↦ᵣ r17) ** (.x6 ↦ᵣ r6))
      ((.x0 ↦ᵣ 0) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) ** (.x17 ↦ᵣ (top - bottom)) **
       (.x6 ↦ᵣ ((0 : Word) + signExtend12 o32))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Exchange two adjacent stack words. -/
theorem swap_limbs (o0 o1 o2 o3 p0 p1 p2 p3 : BitVec 12)
    (base top a0 a1 a2 a3 b0 b1 b2 b3 r17 r5 r31 r30 r29 r28 r6 : Word) :
    cpsTripleWithin 16 base (base + 64) (CodeReq.ofProg base [
      .LD .x17 .x13 p0, .LD .x5 .x13 o0, .LD .x31 .x13 p1, .LD .x30 .x13 o1,
      .LD .x29 .x13 p2, .LD .x28 .x13 o2, .LD .x6 .x13 p3, .SD .x13 .x17 o0,
      .LD .x17 .x13 o3, .SD .x13 .x5 p0, .SD .x13 .x31 o1, .SD .x13 .x30 p1,
      .SD .x13 .x29 o2, .SD .x13 .x28 p2, .SD .x13 .x6 o3, .SD .x13 .x17 p3])
      ((.x13 ↦ᵣ top) ** (.x17 ↦ᵣ r17) ** (.x5 ↦ᵣ r5) ** (.x31 ↦ᵣ r31) ** (.x30 ↦ᵣ r30) **
       (.x29 ↦ᵣ r29) ** (.x28 ↦ᵣ r28) ** (.x6 ↦ᵣ r6) **
       ((top + signExtend12 o0) ↦ₘ b0) ** ((top + signExtend12 o1) ↦ₘ b1) **
       ((top + signExtend12 o2) ↦ₘ b2) ** ((top + signExtend12 o3) ↦ₘ b3) **
       ((top + signExtend12 p0) ↦ₘ a0) ** ((top + signExtend12 p1) ↦ₘ a1) **
       ((top + signExtend12 p2) ↦ₘ a2) ** ((top + signExtend12 p3) ↦ₘ a3))
      ((.x13 ↦ᵣ top) ** (.x17 ↦ᵣ b3) ** (.x5 ↦ᵣ b0) ** (.x31 ↦ᵣ a1) ** (.x30 ↦ᵣ b1) **
       (.x29 ↦ᵣ a2) ** (.x28 ↦ᵣ b2) ** (.x6 ↦ᵣ a3) **
       ((top + signExtend12 o0) ↦ₘ a0) ** ((top + signExtend12 o1) ↦ₘ a1) **
       ((top + signExtend12 o2) ↦ₘ a2) ** ((top + signExtend12 o3) ↦ₘ a3) **
       ((top + signExtend12 p0) ↦ₘ b0) ** ((top + signExtend12 p1) ↦ₘ b1) **
       ((top + signExtend12 p2) ↦ₘ b2) ** ((top + signExtend12 p3) ↦ₘ b3)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Dispatch tail that leaves the stack pointer alone. -/
theorem dispatch_load_keep (oZero oIp oFrame : BitVec 12) (base ip sp entryAddr h : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .LD .x16 .x16 oZero, .ADDI .x15 .x15 oIp, .ADDI .x2 .x2 oFrame])
      ((.x15 ↦ᵣ ip) ** (.x2 ↦ᵣ sp) ** (.x16 ↦ᵣ entryAddr) **
       ((entryAddr + signExtend12 oZero) ↦ₘ h))
      ((.x15 ↦ᵣ (ip + signExtend12 oIp)) ** (.x2 ↦ᵣ (sp + signExtend12 oFrame)) ** (.x16 ↦ᵣ h) **
       ((entryAddr + signExtend12 oZero) ↦ₘ h)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem swap1_spec
    (base sp ra slot gas top bottom ip cw cwAddr entryAddr h : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 r5 r6 r16 r17 r28 r29 r30 r31 : Word)
    (mslot m0 m1 m2 m3 n0 n1 n2 n3 tcell : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (h_m0 : top + signExtend12 0xfc0#12 = m0) (h_m1 : top + signExtend12 0xfc8#12 = m1)
    (h_m2 : top + signExtend12 0xfd0#12 = m2) (h_m3 : top + signExtend12 0xfd8#12 = m3)
    (h_n0 : top + signExtend12 0xfe0#12 = n0) (h_n1 : top + signExtend12 0xfe8#12 = n1)
    (h_n2 : top + signExtend12 0xff0#12 = n2) (h_n3 : top + signExtend12 0xff8#12 = n3)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffd#12) 0)
    (hdepth : BitVec.slt ((0 : Word) + signExtend12 0x020#12) (top - bottom))
    (halign : alignToDword (ip + signExtend12 0x001#12) = cwAddr)
    (hvalid : isValidByteAccess (ip + signExtend12 0x001#12) = true)
    (hent : base + (96 : Word) + (((0x1ffff#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0x178#12 + (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat) = entryAddr) :
    cpsTripleWithin 33 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_swap_1.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) ** (.x5 ↦ᵣ r5) **
       (.x6 ↦ᵣ r6) ** (.x28 ↦ᵣ r28) ** (.x29 ↦ᵣ r29) ** (.x30 ↦ᵣ r30) ** (.x31 ↦ᵣ r31) **
       (mslot ↦ₘ slot) **
       (m0 ↦ₘ b0) ** (m1 ↦ₘ b1) ** (m2 ↦ₘ b2) ** (m3 ↦ₘ b3) **
       (n0 ↦ₘ a0) ** (n1 ↦ₘ a1) ** (n2 ↦ₘ a2) ** (n3 ↦ₘ a3) **
       (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) **
       (.x2 ↦ᵣ (sp + signExtend12 0xff0#12 + signExtend12 0x010#12)) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ (gas + signExtend12 0xffd#12)) ** (.x15 ↦ᵣ (ip + signExtend12 0x001#12)) **
       (.x16 ↦ᵣ h) ** (.x17 ↦ᵣ (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat)) ** (.x5 ↦ᵣ b0) **
       (.x6 ↦ᵣ a3) ** (.x28 ↦ᵣ b2) ** (.x29 ↦ᵣ a2) ** (.x30 ↦ᵣ b1) ** (.x31 ↦ᵣ a1) **
       (mslot ↦ₘ ra) **
       (m0 ↦ₘ a0) ** (m1 ↦ₘ a1) ** (m2 ↦ₘ a2) ** (m3 ↦ₘ a3) **
       (n0 ↦ₘ b0) ** (n1 ↦ₘ b1) ** (n2 ↦ₘ b2) ** (n3 ↦ₘ b3) **
       (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h)) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base sp ra slot gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0078#13 (gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have h1 := depth_swap 0x020#12 (base + 16) top bottom r17 r6
  have hbge := cpsBranchWithin_ntakenStripPure2
    (bge_spec_gen_within .x6 .x17 0x0074#13 ((0 : Word) + signExtend12 0x020#12) (top - bottom) (base + 24))
    (fun hp hq => (pure_end2 hp hq) hdepth)
  have h2 := swap_limbs 0xfc0#12 0xfc8#12 0xfd0#12 0xfd8#12 0xfe0#12 0xfe8#12 0xff0#12 0xff8#12
    (base + 28) top a0 a1 a2 a3 b0 b1 b2 b3 (top - bottom) r5 r31 r30 r29 r28
    ((0 : Word) + signExtend12 0x020#12)
  have hl := lbu_spec_gen_within .x17 .x15 ip b3 0x001#12 (base + 92) cwAddr cw
    (by decide) halign hvalid
  have h3 := dispatch_addr 0x008#12 0x178#12 0x1ffff#20 (base + 96) (sp + signExtend12 0xff0#12) ra
    r16 ((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) ra
  rw [hent] at h3
  have h4 := dispatch_load_keep 0x000#12 0x001#12 0x010#12 (base + 116) ip
    (sp + signExtend12 0xff0#12) entryAddr h
  have hj := jalr_x0_spec_gen_within .x16 h 0x000#12 (base + 128)
  rw [h_mslot] at h0 h3
  rw [h_m0, h_m1, h_m2, h_m3, h_n0, h_n1, h_n2, h_n3] at h2
  rw [h_tcell] at h4
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_swap_1.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hblt := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_swap_1.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_swap_1.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) h1
  have hbge := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_swap_1.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hbge
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 28) Image.f_swap_1.prog _ 7 (by rfl) (by decide) (by decide) (by decide)) h2
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_swap_1.prog 23 (base + 92) (by decide) (by decide) (by rfl))) hl
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 96) Image.f_swap_1.prog _ 24 (by rfl) (by decide) (by decide) (by decide)) h3
  have h4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 116) Image.f_swap_1.prog _ 29 (by rfl) (by decide) (by decide) (by decide)) h4
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_swap_1.prog 32 (base + 128) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hblt h1 hbge h2 hl h3 h4 hj

end PureInterp.Handlers
