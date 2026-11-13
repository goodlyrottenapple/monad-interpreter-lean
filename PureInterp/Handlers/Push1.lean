import PureInterp.Handlers.Add

/-!
# The PUSH1 handler

`f_push_1`, 28 instructions. Fall-through path: at least 3 gas and room for
one more stack slot. The handler reads two bytecode bytes (the immediate and
the next opcode); the model's memory is doubleword-granular, so there is one
theorem for each way those two bytes can fall into doublewords.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-- Stack-room computation: the limit constant and the current depth in bytes. -/
theorem room (hi : BitVec 20) (o : BitVec 12) (base top bottom r16 r17 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .LUI .x17 hi, .SUB .x16 .x13 .x12, .ADDI .x17 .x17 o])
      ((.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17))
      ((.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) ** (.x16 ↦ᵣ (top - bottom)) **
       (.x17 ↦ᵣ (((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 o))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Write a one-limb value to a fresh stack slot. -/
theorem push_store (q1 q2 q0 q3 : BitVec 12) (base top v c1 c2 c0 c3 : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .SD .x13 .x0 q1, .SD .x13 .x0 q2, .SD .x13 .x16 q0, .SD .x13 .x0 q3])
      ((.x0 ↦ᵣ 0) ** (.x13 ↦ᵣ top) ** (.x16 ↦ᵣ v) **
       ((top + signExtend12 q0) ↦ₘ c0) ** ((top + signExtend12 q1) ↦ₘ c1) **
       ((top + signExtend12 q2) ↦ₘ c2) ** ((top + signExtend12 q3) ↦ₘ c3))
      ((.x0 ↦ᵣ 0) ** (.x13 ↦ᵣ top) ** (.x16 ↦ᵣ v) **
       ((top + signExtend12 q0) ↦ₘ v) ** ((top + signExtend12 q1) ↦ₘ 0) **
       ((top + signExtend12 q2) ↦ₘ 0) ** ((top + signExtend12 q3) ↦ₘ 0)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Fall-through path of PUSH1 when the immediate byte and the next opcode byte share a doubleword. -/
theorem push1_spec_same
    (base sp ra slot gas top bottom ip cw1 cwAddr1 entryAddr h r16 r17 : Word)
    (c0 c1 c2 c3 mslot t0 t1 t2 t3 tcell : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (h_t0 : top + signExtend12 0x000#12 = t0) (h_t1 : top + signExtend12 0x008#12 = t1)
    (h_t2 : top + signExtend12 0x010#12 = t2) (h_t3 : top + signExtend12 0x018#12 = t3)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffd#12) 0)
    (hroom : ¬ BitVec.slt ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (top - bottom))
    (halign1 : alignToDword (ip + signExtend12 0x001#12) = cwAddr1)
    (hvalid1 : isValidByteAccess (ip + signExtend12 0x001#12) = true)
    (halign2 : alignToDword (ip + signExtend12 0x002#12) = cwAddr1)
    (hvalid2 : isValidByteAccess (ip + signExtend12 0x002#12) = true)
    (hent : base + (56 : Word) + (((0x1fffa#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0xd0c#12 + (((extractByte cw1 (byteOffset (ip + signExtend12 0x002#12))).zeroExtend 64) <<< (0x03#6).toNat) = entryAddr) :
    cpsTripleWithin 24 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_push_1.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) **
       (mslot ↦ₘ slot) ** (t0 ↦ₘ c0) ** (t1 ↦ₘ c1) ** (t2 ↦ₘ c2) ** (t3 ↦ₘ c3) **
       (cwAddr1 ↦ₘ cw1) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) **
       (.x2 ↦ᵣ (sp + signExtend12 0xff0#12 + signExtend12 0x010#12)) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ (top + signExtend12 0x020#12)) **
       (.x14 ↦ᵣ (gas + signExtend12 0xffd#12)) ** (.x15 ↦ᵣ (ip + signExtend12 0x002#12)) **
       (.x16 ↦ᵣ h) ** (.x17 ↦ᵣ (((extractByte cw1 (byteOffset (ip + signExtend12 0x002#12))).zeroExtend 64) <<< (0x03#6).toNat)) **
       (mslot ↦ₘ ra) ** (t0 ↦ₘ ((extractByte cw1 (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64)) ** (t1 ↦ₘ 0) ** (t2 ↦ₘ 0) ** (t3 ↦ₘ 0) **
       (cwAddr1 ↦ₘ cw1) ** (tcell ↦ₘ h)) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base sp ra slot gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0054#13 (gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have h1 := room 0x00008#20 0xfe0#12 (base + 16) top bottom r16 r17
  have hblt2 := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x17 .x16 0x004c#13 ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (top - bottom) (base + 28))
    (fun hp hq => hroom (pure_end2 hp hq))
  have hl1 := lbu_spec_gen_within .x16 .x15 ip (top - bottom) 0x001#12 (base + 32) cwAddr1 cw1
    (by decide) halign1 hvalid1
  have h2 := push_store 0x008#12 0x010#12 0x000#12 0x018#12 (base + 36) top ((extractByte cw1 (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) c1 c2 c0 c3
  have hl2 := lbu_spec_gen_within .x17 .x15 ip ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) 0x002#12 (base + 52) cwAddr1 cw1
    (by decide) halign2 hvalid2
  have h3 := dispatch_addr 0x008#12 0xd0c#12 0x1fffa#20 (base + 56) (sp + signExtend12 0xff0#12) ra
    ((extractByte cw1 (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) ((extractByte cw1 (byteOffset (ip + signExtend12 0x002#12))).zeroExtend 64) ra
  rw [hent] at h3
  have h4 := dispatch_load 0x000#12 0x020#12 0x002#12 0x010#12 (base + 76) ip top
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

/-- Fall-through path of PUSH1 when the immediate byte and the next opcode byte lie in different doublewords. -/
theorem push1_spec_split
    (base sp ra slot gas top bottom ip cw1 cwAddr1 cw2 cwAddr2 entryAddr h r16 r17 : Word)
    (c0 c1 c2 c3 mslot t0 t1 t2 t3 tcell : Word)
    (h_mslot : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = mslot)
    (h_t0 : top + signExtend12 0x000#12 = t0) (h_t1 : top + signExtend12 0x008#12 = t1)
    (h_t2 : top + signExtend12 0x010#12 = t2) (h_t3 : top + signExtend12 0x018#12 = t3)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xffd#12) 0)
    (hroom : ¬ BitVec.slt ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (top - bottom))
    (halign1 : alignToDword (ip + signExtend12 0x001#12) = cwAddr1)
    (hvalid1 : isValidByteAccess (ip + signExtend12 0x001#12) = true)
    (halign2 : alignToDword (ip + signExtend12 0x002#12) = cwAddr2)
    (hvalid2 : isValidByteAccess (ip + signExtend12 0x002#12) = true)
    (hent : base + (56 : Word) + (((0x1fffa#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0xd0c#12 + (((extractByte cw2 (byteOffset (ip + signExtend12 0x002#12))).zeroExtend 64) <<< (0x03#6).toNat) = entryAddr) :
    cpsTripleWithin 24 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_push_1.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ top) **
       (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) **
       (mslot ↦ₘ slot) ** (t0 ↦ₘ c0) ** (t1 ↦ₘ c1) ** (t2 ↦ₘ c2) ** (t3 ↦ₘ c3) **
       (cwAddr1 ↦ₘ cw1) ** (cwAddr2 ↦ₘ cw2) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) **
       (.x2 ↦ᵣ (sp + signExtend12 0xff0#12 + signExtend12 0x010#12)) **
       (.x12 ↦ᵣ bottom) ** (.x13 ↦ᵣ (top + signExtend12 0x020#12)) **
       (.x14 ↦ᵣ (gas + signExtend12 0xffd#12)) ** (.x15 ↦ᵣ (ip + signExtend12 0x002#12)) **
       (.x16 ↦ᵣ h) ** (.x17 ↦ᵣ (((extractByte cw2 (byteOffset (ip + signExtend12 0x002#12))).zeroExtend 64) <<< (0x03#6).toNat)) **
       (mslot ↦ₘ ra) ** (t0 ↦ₘ ((extractByte cw1 (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64)) ** (t1 ↦ₘ 0) ** (t2 ↦ₘ 0) ** (t3 ↦ₘ 0) **
       (cwAddr1 ↦ₘ cw1) ** (cwAddr2 ↦ₘ cw2) ** (tcell ↦ₘ h)) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base sp ra slot gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0054#13 (gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have h1 := room 0x00008#20 0xfe0#12 (base + 16) top bottom r16 r17
  have hblt2 := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x17 .x16 0x004c#13 ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (top - bottom) (base + 28))
    (fun hp hq => hroom (pure_end2 hp hq))
  have hl1 := lbu_spec_gen_within .x16 .x15 ip (top - bottom) 0x001#12 (base + 32) cwAddr1 cw1
    (by decide) halign1 hvalid1
  have h2 := push_store 0x008#12 0x010#12 0x000#12 0x018#12 (base + 36) top ((extractByte cw1 (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) c1 c2 c0 c3
  have hl2 := lbu_spec_gen_within .x17 .x15 ip ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) 0x002#12 (base + 52) cwAddr2 cw2
    (by decide) halign2 hvalid2
  have h3 := dispatch_addr 0x008#12 0xd0c#12 0x1fffa#20 (base + 56) (sp + signExtend12 0xff0#12) ra
    ((extractByte cw1 (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) ((extractByte cw2 (byteOffset (ip + signExtend12 0x002#12))).zeroExtend 64) ra
  rw [hent] at h3
  have h4 := dispatch_load 0x000#12 0x020#12 0x002#12 0x010#12 (base + 76) ip top
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

end PureInterp.Handlers
