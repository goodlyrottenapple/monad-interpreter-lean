import RiscvZkvm.Rv64.Logic
import PureInterp.Image.Index
import PureInterp.Handlers.Add

/-!
# The SUB handler

`monad::vm::interpreter::sub<Cancun>`, 48 instructions, the same shape as ADD:
this file proves its fall-through path (enough gas, at least two operands).
`a` is the top word and `b` the one below it; the handler stores the limbs of
`a - b` in `b`'s slot. Unlike ADD it uses `t2` (`x7`).
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-! ## Blocks -/

theorem sub_limbs (o0 o1 o2 o3 p0 p1 p2 p3 : BitVec 12) (base t a0 a1 a2 a3 b0 b1 b2 b3 r6 r7 r16 r17 r28 r29 r30 r31 r5 : Word) :
    cpsTripleWithin 26 base (base + 104) (CodeReq.ofProg base [
      .LD .x6 .x13 o1,
      .LD .x29 .x13 p0,
      .LD .x30 .x13 o0,
      .LD .x16 .x13 p1,
      .LD .x31 .x13 o2,
      .LD .x17 .x13 p2,
      .SUB .x28 .x16 .x6,
      .SLTU .x5 .x29 .x30,
      .SLTU .x16 .x16 .x6,
      .SLTU .x6 .x28 .x5,
      .LD .x7 .x13 o3,
      .OR .x16 .x16 .x6,
      .LD .x6 .x13 p3,
      .SUB .x30 .x29 .x30,
      .SUB .x29 .x28 .x5,
      .SUB .x28 .x17 .x31,
      .SLTU .x17 .x17 .x31,
      .SLTU .x31 .x28 .x16,
      .OR .x17 .x17 .x31,
      .SUB .x6 .x6 .x7,
      .SUB .x28 .x28 .x16,
      .SUB .x16 .x6 .x17,
      .SD .x13 .x16 o3,
      .SD .x13 .x30 o0,
      .SD .x13 .x29 o1,
      .SD .x13 .x28 o2])
      ((.x13 ↦ᵣ t) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) ** (.x28 ↦ᵣ r28) **
       (.x29 ↦ᵣ r29) ** (.x30 ↦ᵣ r30) ** (.x31 ↦ᵣ r31) ** (.x5 ↦ᵣ r5) **
       ((t + signExtend12 o0) ↦ₘ b0) ** ((t + signExtend12 o1) ↦ₘ b1) **
       ((t + signExtend12 o2) ↦ₘ b2) ** ((t + signExtend12 o3) ↦ₘ b3) **
       ((t + signExtend12 p0) ↦ₘ a0) ** ((t + signExtend12 p1) ↦ₘ a1) **
       ((t + signExtend12 p2) ↦ₘ a2) ** ((t + signExtend12 p3) ↦ₘ a3))
      ((.x13 ↦ᵣ t) ** (.x6 ↦ᵣ (a3 - b3)) ** (.x7 ↦ᵣ b3) ** (.x16 ↦ᵣ (a3 - b3 - (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))))) **
       (.x17 ↦ᵣ (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) ** (.x28 ↦ᵣ (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) **
       (.x29 ↦ᵣ (a1 - b1 - cb a0 b0)) ** (.x30 ↦ᵣ (a0 - b0)) ** (.x31 ↦ᵣ (cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) ** (.x5 ↦ᵣ cb a0 b0) **
       ((t + signExtend12 o0) ↦ₘ (a0 - b0)) ** ((t + signExtend12 o1) ↦ₘ (a1 - b1 - cb a0 b0)) **
       ((t + signExtend12 o2) ↦ₘ (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) ** ((t + signExtend12 o3) ↦ₘ (a3 - b3 - (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))))) **
       ((t + signExtend12 p0) ↦ₘ a0) ** ((t + signExtend12 p1) ↦ₘ a1) **
       ((t + signExtend12 p2) ↦ₘ a2) ** ((t + signExtend12 p3) ↦ₘ a3)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Fall-through path of the handler: charge gas, subtract the second stack
    word from the top one into the second slot, pop, and jump to the next
    opcode's handler. -/
theorem sub_spec
    (base sp ra slot gas top bottom ip cw cwAddr entryAddr h : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 r5 r6 r7 r16 r17 r28 r29 r30 r31 : Word)
    (mslot m0 m1 m2 m3 n0 n1 n2 n3 tcell : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (h_m0 : top + signExtend12 0xfc0#12 = m0)
    (h_m1 : top + signExtend12 0xfc8#12 = m1)
    (h_m2 : top + signExtend12 0xfd0#12 = m2)
    (h_m3 : top + signExtend12 0xfd8#12 = m3)
    (h_n0 : top + signExtend12 0xfe0#12 = n0)
    (h_n1 : top + signExtend12 0xfe8#12 = n1)
    (h_n2 : top + signExtend12 0xff0#12 = n2)
    (h_n3 : top + signExtend12 0xff8#12 = n3)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffd#12) 0)
    (hdepth : BitVec.slt ((0 : Word) + signExtend12 0x020#12) (top - bottom))
    (halign : alignToDword (ip + signExtend12 0x001#12) = cwAddr)
    (hvalid : isValidByteAccess (ip + signExtend12 0x001#12) = true)
    (hent : base + (136 : Word) + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0x30c#12 +
        (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat) = entryAddr) :
    cpsTripleWithin 44 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_sub.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) ** (.x5 ↦ᵣ r5) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x28 ↦ᵣ r28) ** (.x29 ↦ᵣ r29) ** (.x30 ↦ᵣ r30) ** (.x31 ↦ᵣ r31) **
       (mslot ↦ₘ slot) **
       (m0 ↦ₘ b0) ** (m1 ↦ₘ b1) **
       (m2 ↦ₘ b2) ** (m3 ↦ₘ b3) **
       (n0 ↦ₘ a0) ** (n1 ↦ₘ a1) **
       (n2 ↦ₘ a2) ** (n3 ↦ₘ a3) **
       (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 0xff0#12 + signExtend12 0x010#12)) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ (top + signExtend12 0xfe0#12)) **
       (.x14 ↦ᵣ (gas + signExtend12 0xffd#12)) ** (.x15 ↦ᵣ (ip + signExtend12 0x001#12)) **
       (.x16 ↦ᵣ h) ** (.x17 ↦ᵣ (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat)) **
       (.x5 ↦ᵣ cb a0 b0) **
       (.x6 ↦ᵣ (a3 - b3)) ** (.x7 ↦ᵣ b3) ** (.x28 ↦ᵣ (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) ** (.x29 ↦ᵣ (a1 - b1 - cb a0 b0)) ** (.x30 ↦ᵣ (a0 - b0)) **
       (.x31 ↦ᵣ (cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) **
       (mslot ↦ₘ ra) **
       (m0 ↦ₘ (a0 - b0)) ** (m1 ↦ₘ (a1 - b1 - cb a0 b0)) **
       (m2 ↦ₘ (a2 - b2 - (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))) **
       (m3 ↦ₘ (a3 - b3 - (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))))) **
       (n0 ↦ₘ a0) ** (n1 ↦ₘ a1) **
       (n2 ↦ₘ a2) ** (n3 ↦ₘ a3) **
       (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h)) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base sp ra slot gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x00a4#13 (gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have h1 := depth 0x020#12 (base + 16) top bottom r16 r17
  have hbge := cpsBranchWithin_ntakenStripPure2
    (bge_spec_gen_within .x17 .x16 0x00a0#13 ((0 : Word) + signExtend12 0x020#12) (top - bottom) (base + 24))
    (fun hp hq => (pure_end2 hp hq) hdepth)
  have h2 := sub_limbs 0xfc0#12 0xfc8#12 0xfd0#12 0xfd8#12 0xfe0#12 0xfe8#12 0xff0#12 0xff8#12 (base + 28) top a0 a1 a2 a3 b0 b1 b2 b3
    r6 r7 (top - bottom) ((0 : Word) + signExtend12 0x020#12) r28 r29 r30 r31 r5
  have hl := lbu_spec_gen_within .x17 .x15 ip
    (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0)))
    0x001#12 (base + 132) cwAddr cw (by decide) halign hvalid
  have h3 := dispatch_addr 0x008#12 0x30c#12 0x1fffd#20 (base + 136) (sp + signExtend12 0xff0#12) ra
    (a3 - b3 - (cb a2 b2 ||| cb (a2 - b2) (cb a1 b1 ||| cb (a1 - b1) (cb a0 b0))))
    ((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) ra
  rw [hent] at h3
  have h4 := dispatch_load 0x000#12 0xfe0#12 0x001#12 0x010#12 (base + 156) ip top (sp + signExtend12 0xff0#12) entryAddr h
  have hj := jalr_x0_spec_gen_within .x16 h 0x000#12 (base + 172)
  rw [h_mslot] at h0 h3
  rw [h_m0, h_m1, h_m2, h_m3, h_n0, h_n1, h_n2, h_n3] at h2
  rw [h_tcell] at h4
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_sub.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hblt := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_sub.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) h1
  have hbge := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hbge
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 28) Image.f_sub.prog _ 7 (by rfl) (by decide) (by decide) (by decide)) h2
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 33 (base + 132) (by decide) (by decide) (by rfl))) hl
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 136) Image.f_sub.prog _ 34 (by rfl) (by decide) (by decide) (by decide)) h3
  have h4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 156) Image.f_sub.prog _ 39 (by rfl) (by decide) (by decide) (by decide)) h4
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 43 (base + 172) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hblt h1 hbge h2 hl h3 h4 hj

end PureInterp.Handlers
