import RiscvZkvm.Rv64.Logic
import PureInterp.Image.Index

/-!
# `core_loop`

The function the trampoline calls: load the instruction pointer from the
intercode object and the gas from the context, shuffle the arguments into the
handler calling convention (`a0` context, `a1` intercode, `a2` stack bottom,
`a3` stack top, `a4` gas, `a5` instruction pointer) and tail-jump to the
table entry of the first opcode byte.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem core_loop_head (oA oM : BitVec 12) (base r10 ctx an r15 ip : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .LD .x15 .x12 oA, .ADDI .x10 .x11 oM])
      ((.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ ctx) ** (.x12 ↦ᵣ an) ** (.x15 ↦ᵣ r15) **
       ((an + signExtend12 oA) ↦ₘ ip))
      ((.x10 ↦ᵣ (ctx + signExtend12 oM)) ** (.x11 ↦ᵣ ctx) ** (.x12 ↦ᵣ an) ** (.x15 ↦ᵣ ip) **
       ((an + signExtend12 oA) ↦ₘ ip)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem table_addr (oLo : BitVec 12) (hi : BitVec 20) (base r16 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .AUIPC .x16 hi, .ADDI .x16 .x16 oLo])
      (.x16 ↦ᵣ r16)
      (.x16 ↦ᵣ (base + ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 oLo)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem core_loop_tail (oG oZ oA oS : BitVec 12) (base c10 opc an stk r14 tb gas h : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base [
      .LD .x14 .x10 oG, .SLLI .x11 .x11 0x03#6, .ADD .x16 .x16 .x11, .LD .x16 .x16 oZ,
      .ADDI .x11 .x12 oA, .ADDI .x12 .x13 oS])
      ((.x10 ↦ᵣ c10) ** (.x11 ↦ᵣ opc) ** (.x12 ↦ᵣ an) ** (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ r14) **
       (.x16 ↦ᵣ tb) ** ((c10 + signExtend12 oG) ↦ₘ gas) **
       ((tb + (opc <<< (0x03#6).toNat) + signExtend12 oZ) ↦ₘ h))
      ((.x10 ↦ᵣ c10) ** (.x11 ↦ᵣ (an + signExtend12 oA)) ** (.x12 ↦ᵣ (stk + signExtend12 oS)) **
       (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ gas) ** (.x16 ↦ᵣ h) ** ((c10 + signExtend12 oG) ↦ₘ gas) **
       ((tb + (opc <<< (0x03#6).toNat) + signExtend12 oZ) ↦ₘ h)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- `core_loop(_, ctx, analysis, stack, _)`: ends at the table entry `h` of the
    first opcode byte, with the registers of the handler calling convention.
    The opcode byte is read from the doubleword `cwAddr ↦ₘ cw` that contains
    the instruction pointer `ip`. -/
theorem core_loop_spec (base r10 ctx an stk r14 r15 r16 ip cw cwAddr gas h : Word)
    (acell gcell tcell : Word)
    (h_acell : an + signExtend12 0x000#12 = acell)
    (h_gcell : ctx + signExtend12 0x000#12 + signExtend12 0x008#12 = gcell)
    (halign : alignToDword (ip + signExtend12 0x000#12) = cwAddr)
    (hvalid : isValidByteAccess (ip + signExtend12 0x000#12) = true)
    (h_tcell : base + (8 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0x140#12 +
        (((extractByte cw (byteOffset (ip + signExtend12 0x000#12))).zeroExtend 64) <<< (0x03#6).toNat) +
        signExtend12 0x000#12 = tcell) :
    cpsTripleWithin 12 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_core_loop.prog)
      ((.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ ctx) ** (.x12 ↦ᵣ an) ** (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) ** (.x16 ↦ᵣ r16) ** (acell ↦ₘ ip) ** (cwAddr ↦ₘ cw) ** (gcell ↦ₘ gas) **
       (tcell ↦ₘ h))
      ((.x10 ↦ᵣ (ctx + signExtend12 0x000#12)) ** (.x11 ↦ᵣ (an + signExtend12 0x000#12)) **
       (.x12 ↦ᵣ (stk + signExtend12 0x000#12)) ** (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ gas) **
       (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ h) ** (acell ↦ₘ ip) ** (cwAddr ↦ₘ cw) ** (gcell ↦ₘ gas) **
       (tcell ↦ₘ h)) := by
  have h0 := core_loop_head 0x000#12 0x000#12 base r10 ctx an r15 ip
  have ht := table_addr 0x140#12 0x20000#20 (base + 8) r16
  have hl := lbu_spec_gen_within .x11 .x15 ip ctx 0x000#12 (base + 16) cwAddr cw
    (by decide) halign hvalid
  have h1 := core_loop_tail 0x008#12 0x000#12 0x000#12 0x000#12 (base + 20)
    (ctx + signExtend12 0x000#12)
    ((extractByte cw (byteOffset (ip + signExtend12 0x000#12))).zeroExtend 64) an stk r14
    (base + (8 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0x140#12)
    gas h
  have hj := jalr_x0_spec_gen_within .x16 h 0x000#12 (base + 44)
  rw [h_acell] at h0
  rw [h_gcell, h_tcell] at h1
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_core_loop.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have ht := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 8) Image.f_core_loop.prog _ 2 (by rfl) (by decide) (by decide) (by decide)) ht
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_core_loop.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hl
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 20) Image.f_core_loop.prog _ 5 (by rfl) (by decide) (by decide) (by decide)) h1
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_core_loop.prog 11 (base + 44) (by decide) (by decide) (by rfl))) hj
  runBlock h0 ht hl h1 hj

end PureInterp.Entry
