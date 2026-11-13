import PureInterp.Machine.Full

/-!
# Exceptional halts

Each handler's out-of-gas and stack-check paths, followed from the invariant
through `Context::exit` and `longjmp` to the `setjmp` return site. The status
stored is 3 for out of gas and 2 for a stack error; the context's gas field is
left as it was.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

theorem li_a1 (e : BitVec 12) (base r11 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x11 .x0 e])
      ((.x0 ↦ᵣ 0) ** (.x11 ↦ᵣ r11)) ((.x0 ↦ᵣ 0) ** (.x11 ↦ᵣ ((0 : Word) + signExtend12 e))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- ADD without enough gas. -/
theorem add_oog_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_add.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 180 + signExtend21 0x007de4#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0) :
    cpsTripleWithin 30 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffd#12) (base + 180 + 4) ((0 : Word) + signExtend12 0x003#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_takenStripPure2
    (blt_spec_gen_within .x14 .x0 0x00a4#13 (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => (pure_end2 hp hq) hgas)
  have e1 : base + 12 + signExtend13 0x00a4#13 = base + 176 := by rv64_addr
  rw [e1] at hblt
  have hli := li_a1 0x003#12 (base + 176) a1v
  have hj := jal_spec_within .x1 L.ra 0x007de4#21 (base + 180) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 180 + 4)
    ((0 : Word) + signExtend12 0x003#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_add.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_add.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 176) Image.f_add.prog _ 44 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_add.prog 45 (base + 180) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hli hj hx

/-- ADD with fewer than two operands. -/
theorem add_err_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_add.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 188 + signExtend21 0x007ddc#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : ¬ BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0)
    (hdepth : ¬ BitVec.slt ((0 : Word) + signExtend12 0x020#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom)) :
    cpsTripleWithin 33 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra, r16 := (L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom, r17 := (0 : Word) + signExtend12 0x020#12 } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffd#12) (base + 188 + 4) ((0 : Word) + signExtend12 0x002#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x00a4#13 (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have hd := Handlers.depth 0x020#12 (base + 16) (L.bottom + BitVec.ofNat 64 (32 * depth)) L.bottom scr.r16 scr.r17
  have hbr := cpsBranchWithin_takenStripPure2
    (bge_spec_gen_within .x17 .x16 0x00a0#13 ((0 : Word) + signExtend12 0x020#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom) (base + 24))
    (fun hp hq => hdepth (pure_end2 hp hq))
  have e1 : base + 24 + signExtend13 0x00a0#13 = base + 184 := by rv64_addr
  rw [e1] at hbr
  have hli := li_a1 0x002#12 (base + 184) a1v
  have hj := jal_spec_within .x1 L.ra 0x007ddc#21 (base + 188) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 188 + 4)
    ((0 : Word) + signExtend12 0x002#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_add.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_add.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hd := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_add.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hd)
  have hbr := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_add.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hbr)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 184) Image.f_add.prog _ 46 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_add.prog 47 (base + 188) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hd hbr hli hj hx

/-- POP without enough gas. -/
theorem pop_oog_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_pop.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 72 + signExtend21 0x00a840#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffe#12) 0) :
    cpsTripleWithin 30 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffe#12) (base + 72 + 4) ((0 : Word) + signExtend12 0x003#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffe#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_takenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0038#13 (BitVec.ofNat 64 gas + signExtend12 0xffe#12) 0 (base + 12))
    (fun hp hq => (pure_end2 hp hq) hgas)
  have e1 : base + 12 + signExtend13 0x0038#13 = base + 68 := by rv64_addr
  rw [e1] at hblt
  have hli := li_a1 0x003#12 (base + 68) a1v
  have hj := jal_spec_within .x1 L.ra 0x00a840#21 (base + 72) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 72 + 4)
    ((0 : Word) + signExtend12 0x003#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_pop.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 68) Image.f_pop.prog _ 17 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 18 (base + 72) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hli hj hx

/-- POP on an empty stack. -/
theorem pop_err_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_pop.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 80 + signExtend21 0x00a838#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : ¬ BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffe#12) 0)
    (hdepth : ¬ BitVec.slt (0 : Word) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom)) :
    cpsTripleWithin 32 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra, r16 := (L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffe#12) (base + 80 + 4) ((0 : Word) + signExtend12 0x002#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffe#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0038#13 (BitVec.ofNat 64 gas + signExtend12 0xffe#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have hd := sub_spec_gen_within .x16 .x13 .x12 (L.bottom + BitVec.ofNat 64 (32 * depth)) L.bottom scr.r16 (base + 16) (by decide)
  have hbr := cpsBranchWithin_takenStripPure2
    (bge_spec_gen_within .x0 .x16 0x0038#13 (0 : Word) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom) (base + 20))
    (fun hp hq => hdepth (pure_end2 hp hq))
  have e1 : base + 20 + signExtend13 0x0038#13 = base + 76 := by rv64_addr
  rw [e1] at hbr
  have hli := li_a1 0x002#12 (base + 76) a1v
  have hj := jal_spec_within .x1 L.ra 0x00a838#21 (base + 80) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 80 + 4)
    ((0 : Word) + signExtend12 0x002#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_pop.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hd := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hd)
  have hbr := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 5 (base + 20) (by decide) (by decide) (by rfl))) hbr)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 76) Image.f_pop.prog _ 19 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_pop.prog 20 (base + 80) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hd hbr hli hj hx

/-- PUSH1 without enough gas. -/
theorem push1_oog_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_push_1.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 100 + signExtend21 0x0048a4#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0) :
    cpsTripleWithin 30 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffd#12) (base + 100 + 4) ((0 : Word) + signExtend12 0x003#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_takenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0054#13 (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => (pure_end2 hp hq) hgas)
  have e1 : base + 12 + signExtend13 0x0054#13 = base + 96 := by rv64_addr
  rw [e1] at hblt
  have hli := li_a1 0x003#12 (base + 96) a1v
  have hj := jal_spec_within .x1 L.ra 0x0048a4#21 (base + 100) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 100 + 4)
    ((0 : Word) + signExtend12 0x003#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_push_1.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 96) Image.f_push_1.prog _ 24 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 25 (base + 100) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hli hj hx

/-- PUSH1 on a full stack. -/
theorem push1_ovf_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_push_1.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 108 + signExtend21 0x00489c#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : ¬ BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0)
    (hroom : BitVec.slt ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom)) :
    cpsTripleWithin 34 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra, r16 := (L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom, r17 := ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffd#12) (base + 108 + 4) ((0 : Word) + signExtend12 0x002#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x0054#13 (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have hd := room 0x00008#20 0xfe0#12 (base + 16) (L.bottom + BitVec.ofNat 64 (32 * depth)) L.bottom scr.r16 scr.r17
  have hbr := cpsBranchWithin_takenStripPure2
    (blt_spec_gen_within .x17 .x16 0x004c#13 ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom) (base + 28))
    (fun hp hq => (pure_end2 hp hq) hroom)
  have e1 : base + 28 + signExtend13 0x004c#13 = base + 104 := by rv64_addr
  rw [e1] at hbr
  have hli := li_a1 0x002#12 (base + 104) a1v
  have hj := jal_spec_within .x1 L.ra 0x00489c#21 (base + 108) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 108 + 4)
    ((0 : Word) + signExtend12 0x002#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_push_1.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hd := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_push_1.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hd)
  have hbr := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 7 (base + 28) (by decide) (by decide) (by rfl))) hbr)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 104) Image.f_push_1.prog _ 26 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_push_1.prog 27 (base + 108) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hd hbr hli hj hx

/-- SUB without enough gas. -/
theorem sub_oog_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_sub.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 180 + signExtend21 0x007ea4#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0) :
    cpsTripleWithin 30 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffd#12) (base + 180 + 4) ((0 : Word) + signExtend12 0x003#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_takenStripPure2
    (blt_spec_gen_within .x14 .x0 0x00a4#13 (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => (pure_end2 hp hq) hgas)
  have e1 : base + 12 + signExtend13 0x00a4#13 = base + 176 := by rv64_addr
  rw [e1] at hblt
  have hli := li_a1 0x003#12 (base + 176) a1v
  have hj := jal_spec_within .x1 L.ra 0x007ea4#21 (base + 180) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 180 + 4)
    ((0 : Word) + signExtend12 0x003#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_sub.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 176) Image.f_sub.prog _ 44 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 45 (base + 180) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hli hj hx

/-- SUB with fewer than two operands. -/
theorem sub_err_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_sub.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 188 + signExtend21 0x007e9c#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2)
    (hgas : ¬ BitVec.slt (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0)
    (hdepth : ¬ BitVec.slt ((0 : Word) + signExtend12 0x020#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom)) :
    cpsTripleWithin 33 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra, r16 := (L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom, r17 := (0 : Word) + signExtend12 0x020#12 } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas + signExtend12 0xffd#12) (base + 188 + 4) ((0 : Word) + signExtend12 0x002#12) g0 res fr) := by
  have h0 := prologue 0xff0#12 0x008#12 0xffd#12 base L.sp L.ra scr.slot (BitVec.ofNat 64 gas)
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl] at h0
  have hblt := cpsBranchWithin_ntakenStripPure2
    (blt_spec_gen_within .x14 .x0 0x00a4#13 (BitVec.ofNat 64 gas + signExtend12 0xffd#12) 0 (base + 12))
    (fun hp hq => hgas (pure_end2 hp hq))
  have hd := Handlers.depth 0x020#12 (base + 16) (L.bottom + BitVec.ofNat 64 (32 * depth)) L.bottom scr.r16 scr.r17
  have hbr := cpsBranchWithin_takenStripPure2
    (bge_spec_gen_within .x17 .x16 0x00a0#13 ((0 : Word) + signExtend12 0x020#12) ((L.bottom + BitVec.ofNat 64 (32 * depth)) - L.bottom) (base + 24))
    (fun hp hq => hdepth (pure_end2 hp hq))
  have e1 : base + 24 + signExtend13 0x00a0#13 = base + 184 := by rv64_addr
  rw [e1] at hbr
  have hli := li_a1 0x002#12 (base + 184) a1v
  have hj := jal_spec_within .x1 L.ra 0x007e9c#21 (base + 188) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 188 + 4)
    ((0 : Word) + signExtend12 0x002#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have h0 := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base) Image.f_sub.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0)
  have hblt := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hblt)
  have hd := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_sub.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hd)
  have hbr := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 6 (base + 24) (by decide) (by decide) (by rfl))) hbr)
  have hli := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 184) Image.f_sub.prog _ 46 (by rfl) (by decide) (by decide) (by decide)) hli)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_sub.prog 47 (base + 188) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock h0 hblt hd hbr hli hj hx

/-- An opcode whose table entry is the `invalid` handler: status 2, with the
    gas at that point written to the context (the result reports none). -/
theorem invalid_final (cr : CodeReq) (L : Layout) (E : ExitEnv) (scr : Scratch) (limbs : List Word)
    (base a1v g0 s2 st0 : Word) (res fr : List Word) (depth gas pc : Nat)
    (hc : ∀ a i, CodeReq.ofProg base Image.f_invalid.prog a = some i → cr a = some i)
    (hce : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_be : base + 16 + signExtend21 0x00accc#21 = E.be)
    (h_bl : E.be + 24 + signExtend21 0x000044#21 = E.bl)
    (h_slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2) :
    cpsTripleWithin 29 base ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
      (interp L scr limbs depth gas pc ** exitFrame E a1v g0 s2 st0 res fr)
      (final L E { scr with slot := L.ra } limbs L.bottom (L.bottom + BitVec.ofNat 64 (32 * depth))
        (BitVec.ofNat 64 gas) (base + 16 + 4) ((0 : Word) + signExtend12 0x002#12)
        (BitVec.ofNat 64 gas) res fr) := by
  have hb := stop_body 0xff0#12 0x002#12 0x008#12 0x008#12 base L.sp L.ra E.ctx
    (BitVec.ofNat 64 gas) a1v g0 scr.slot
  rw [show L.sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = frameSlot L.sp from rfl,
    se_lit_8] at hb
  have hj := jal_spec_within .x1 L.ra 0x00accc#21 (base + 16) (by decide)
  rw [h_be] at hj
  have hx := exit_chain cr E.be E.bl E.ctx (L.sp + signExtend12 0xff0#12) (base + 16 + 4)
    ((0 : Word) + signExtend12 0x002#12) (L.codeBase + BitVec.ofNat 64 pc) E.jb s2 st0 E.slot2
    E.c0 E.c1 E.c2 E.c3 E.c4 E.c5 E.c6 E.c7 E.c8 E.c9 E.c10 E.c11 E.v0 E.v1 E.v2 E.v3 E.v4 E.v5 E.v6 E.v7 E.v8 E.v9 E.v10 E.v11 E.v12 E.v13 hce hcl h_bl h_slot2
  have hb := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_invalid.prog _ 0 (by simp) (by decide) (by decide) (by decide)) hb)
  have hj := cpsTripleWithin_extend_code hc (cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_invalid.prog 4 (base + 16) (by decide) (by decide) (by rfl))) hj)
  unfold interp exitFrame final
  runBlock hb hj hx

end PureInterp.Machine
