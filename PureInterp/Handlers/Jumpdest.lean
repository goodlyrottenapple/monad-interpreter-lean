import PureInterp.Handlers.Exit

/-!
# The JUMPDEST handler

`f_jumpdest`, 14 instructions, no stack frame on the normal path. Both of its
paths are proved: the normal one, and the out-of-gas one followed through
`Context::exit` and `longjmp`.
-/

namespace PureInterp.Handlers
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem charge_only (o : BitVec 12) (base gas : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x14 .x14 o])
      (.x14 ↦ᵣ gas) (.x14 ↦ᵣ (gas + signExtend12 o)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Table address computation without a frame to restore. -/
theorem dispatch_addr_leaf (oLo oIp : BitVec 12) (hi : BitVec 20) (base ip r16 opc : Word) :
    cpsTripleWithin 5 base (base + 20) (CodeReq.ofProg base [
      .AUIPC .x16 hi, .ADDI .x16 .x16 oLo, .ADDI .x15 .x15 oIp,
      .SLLI .x17 .x17 0x03#6, .ADD .x16 .x16 .x17])
      ((.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ opc))
      ((.x15 ↦ᵣ (ip + signExtend12 oIp)) **
       (.x16 ↦ᵣ (base + ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 oLo +
        (opc <<< (0x03#6).toNat))) **
       (.x17 ↦ᵣ (opc <<< (0x03#6).toNat))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem load_entry (oZ : BitVec 12) (base entryAddr h : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.LD .x16 .x16 oZ])
      ((.x16 ↦ᵣ entryAddr) ** ((entryAddr + signExtend12 oZ) ↦ₘ h))
      ((.x16 ↦ᵣ h) ** ((entryAddr + signExtend12 oZ) ↦ₘ h)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Normal path: charge 1 gas and dispatch. -/
theorem jumpdest_spec (base gas ip cw cwAddr entryAddr h r16 r17 tcell : Word)
    (h_tcell : entryAddr + signExtend12 0x000#12 = tcell)
    (hgas : ¬ BitVec.slt (gas + signExtend12 0xfff#12) 0)
    (halign : alignToDword (ip + signExtend12 0x001#12) = cwAddr)
    (hvalid : isValidByteAccess (ip + signExtend12 0x001#12) = true)
    (hent : base + (12 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0xa04#12 + (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat) = entryAddr) :
    cpsTripleWithin 10 base ((h + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_jumpdest.prog)
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ r16) ** (.x17 ↦ᵣ r17) **
       (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ (gas + signExtend12 0xfff#12)) ** (.x15 ↦ᵣ (ip + signExtend12 0x001#12)) **
       (.x16 ↦ᵣ h) ** (.x17 ↦ᵣ (((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64) <<< (0x03#6).toNat)) **
       (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h)) := by
  have h0 := charge_only 0xfff#12 base gas
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0024#13 (gas + signExtend12 0xfff#12) 0 (base + 4))
    (fun hp hq => hgas (pure_end2 hp hq))
  have hl := lbu_spec_gen_within .x17 .x15 ip r17 0x001#12 (base + 8) cwAddr cw
    (by decide) halign hvalid
  have h3 := dispatch_addr_leaf 0xa04#12 0x001#12 0x20000#20 (base + 12) ip r16 ((extractByte cw (byteOffset (ip + signExtend12 0x001#12))).zeroExtend 64)
  rw [hent] at h3
  have h4 := load_entry 0x000#12 (base + 32) entryAddr h
  rw [h_tcell] at h4
  have hj := jalr_x0_spec_gen_within .x16 h 0x000#12 (base + 36)
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_jumpdest.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hblt := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_jumpdest.prog 1 (base + 4) (by decide) (by decide) (by rfl))) hblt
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_jumpdest.prog 2 (base + 8) (by decide) (by decide) (by rfl))) hl
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 12) Image.f_jumpdest.prog _ 3 (by rfl) (by decide) (by decide) (by decide)) h3
  have h4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 32) Image.f_jumpdest.prog _ 8 (by rfl) (by decide) (by decide) (by decide)) h4
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_jumpdest.prog 9 (base + 36) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hblt hl h3 h4 hj

theorem oog_frame (oF oSt oS : BitVec 12) (base sp ra r11 slot : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .ADDI .x2 .x2 oF, .ADDI .x11 .x0 oSt, .SD .x2 .x1 oS])
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x11 ↦ᵣ r11) **
       ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ slot))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp + signExtend12 oF)) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 oSt)) **
       ((sp + signExtend12 oF + signExtend12 oS) ↦ₘ ra)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Out-of-gas path within the handler: up to its call of `Context::exit(3)`. -/
theorem jumpdest_oog (base sp ra gas r11 slot scell : Word)
    (h_scell : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell)
    (hgas : BitVec.slt (gas + signExtend12 0xfff#12) 0) :
    cpsTripleWithin 6 base (base + 52 + signExtend21 0x00a5a0#21)
      (CodeReq.ofProg base Image.f_jumpdest.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x11 ↦ᵣ r11) ** (.x14 ↦ᵣ gas) **
       (scell ↦ₘ slot))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (base + 52 + 4)) ** (.x2 ↦ᵣ (sp + signExtend12 0xff0#12)) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x003#12)) ** (.x14 ↦ᵣ (gas + signExtend12 0xfff#12)) **
       (scell ↦ₘ ra)) := by
  have h0 := charge_only 0xfff#12 base gas
  have hblt := cpsBranchWithin_takenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0024#13 (gas + signExtend12 0xfff#12) 0 (base + 4))
    (fun hp hq => (pure_end2 hp hq) hgas)
  have e : base + 4 + signExtend13 0x0024#13 = base + 40 := by rv64_addr
  rw [e] at hblt
  have h1 := oog_frame 0xff0#12 0x003#12 0x008#12 (base + 40) sp ra r11 slot
  rw [h_scell] at h1
  have hj := jal_spec_within .x1 ra 0x00a5a0#21 (base + 52) (by decide)
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_jumpdest.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hblt := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_jumpdest.prog 1 (base + 4) (by decide) (by decide) (by rfl))) hblt
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 40) Image.f_jumpdest.prog _ 10 (by rfl) (by decide) (by decide) (by decide)) h1
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_jumpdest.prog 13 (base + 52) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hblt h1 hj

/-- Out of gas at a JUMPDEST, followed to the `setjmp` return site: status 3
    (out of gas) is in the context, the callee-saved registers and `sp` are
    restored from the jump buffer, and `a0 = 1`. -/
theorem jumpdest_oog_exit (cr : CodeReq) (base be bl ctx gas r11 r15 slot1 slot2 jb st0 : Word)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 scell1 scell2 jcell stcell : Word)
    (hcj : ∀ a i, CodeReq.ofProg base Image.f_jumpdest.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 52 + signExtend21 0x00a5a0#21 = be)
    (h_bl : be + 24 + signExtend21 0x000044#21 = bl)
    (h_scell1 : r13 + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell1)
    (h_scell2 : (r13 + signExtend12 0xff0#12) + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell2)
    (h_jcell : ctx + signExtend12 0x130#12 = jcell)
    (h_stcell : ctx + signExtend12 0x000#12 + signExtend12 0x0f8#12 = stcell)
    (h_j0 : jb + signExtend12 0x000#12 = j0)
    (h_j1 : jb + signExtend12 0x008#12 = j1)
    (h_j2 : jb + signExtend12 0x010#12 = j2)
    (h_j3 : jb + signExtend12 0x018#12 = j3)
    (h_j4 : jb + signExtend12 0x020#12 = j4)
    (h_j5 : jb + signExtend12 0x028#12 = j5)
    (h_j6 : jb + signExtend12 0x030#12 = j6)
    (h_j7 : jb + signExtend12 0x038#12 = j7)
    (h_j8 : jb + signExtend12 0x040#12 = j8)
    (h_j9 : jb + signExtend12 0x048#12 = j9)
    (h_j10 : jb + signExtend12 0x050#12 = j10)
    (h_j11 : jb + signExtend12 0x058#12 = j11)
    (h_j12 : jb + signExtend12 0x060#12 = j12)
    (h_j13 : jb + signExtend12 0x068#12 = j13)
    (hgas : BitVec.slt (gas + signExtend12 0xfff#12) 0) :
    cpsTripleWithin 30 base ((v0 + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x1 ↦ᵣ r0) ** (.x8 ↦ᵣ r1) ** (.x9 ↦ᵣ r2) ** (.x18 ↦ᵣ r3) ** (.x19 ↦ᵣ r4) **
       (.x20 ↦ᵣ r5) ** (.x21 ↦ᵣ r6) ** (.x22 ↦ᵣ r7) ** (.x23 ↦ᵣ r8) ** (.x24 ↦ᵣ r9) **
       (.x25 ↦ᵣ r10) ** (.x26 ↦ᵣ r11) ** (.x27 ↦ᵣ r12) ** (.x2 ↦ᵣ r13) ** (.x0 ↦ᵣ 0) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ r11) ** (.x14 ↦ᵣ gas) ** (.x15 ↦ᵣ r15) ** (scell1 ↦ₘ slot1) **
       (jcell ↦ₘ jb) ** (scell2 ↦ₘ slot2) ** (stcell ↦ₘ st0) ** (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) **
       (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) **
       (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13))
      ((.x1 ↦ᵣ v0) ** (.x8 ↦ᵣ v1) ** (.x9 ↦ᵣ v2) ** (.x18 ↦ᵣ v3) ** (.x19 ↦ᵣ v4) **
       (.x20 ↦ᵣ v5) ** (.x21 ↦ᵣ v6) ** (.x22 ↦ᵣ v7) ** (.x23 ↦ᵣ v8) ** (.x24 ↦ᵣ v9) **
       (.x25 ↦ᵣ v10) ** (.x26 ↦ᵣ v11) ** (.x27 ↦ᵣ v12) ** (.x2 ↦ᵣ v13) ** (.x0 ↦ᵣ 0) **
       (.x10 ↦ᵣ ((if BitVec.ult ((0 : Word) + signExtend12 0x001#12) (signExtend12 0x001#12) then (1 : Word) else 0) + ((0 : Word) + signExtend12 0x001#12))) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x001#12)) **
       (.x14 ↦ᵣ (gas + signExtend12 0xfff#12)) ** (.x15 ↦ᵣ (ctx + signExtend12 0x000#12)) **
       (scell1 ↦ₘ r0) ** (jcell ↦ₘ jb) ** (scell2 ↦ₘ (base + 52 + 4)) **
       (stcell ↦ₘ ((0 : Word) + signExtend12 0x003#12)) ** (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) **
       (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) **
       (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13)) := by
  have h1 := jumpdest_oog base r13 r0 gas r11 slot1 scell1 h_scell1 hgas
  rw [h_be] at h1
  have h2 := exit_spec be (r13 + signExtend12 0xff0#12) (base + 52 + 4) ctx ((0 : Word) + signExtend12 0x003#12) r15 jb slot2 st0
    jcell scell2 stcell h_jcell h_scell2 h_stcell
  rw [h_bl] at h2
  have h3 := longjmp_spec bl jb ((0 : Word) + signExtend12 0x001#12)
    (be + 24 + 4) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 ((r13 + signExtend12 0xff0#12) + signExtend12 0xff0#12)
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 h_j0 h_j1 h_j2 h_j3 h_j4 h_j5 h_j6 h_j7 h_j8 h_j9 h_j10 h_j11 h_j12 h_j13
  have h1 := cpsTripleWithin_extend_code hcj h1
  have h2 := cpsTripleWithin_extend_code hce h2
  have h3 := cpsTripleWithin_extend_code hcl h3
  runBlock h1 h2 h3

end PureInterp.Handlers
