import PureInterp.Entry.Basic

/-!
# `Context::copy_to_result`, the two failure paths

`copy_to_result(result*, ctx*)` first looks at `ctx->result.status`
(the doubleword at `ctx + 0xf8`, the cell `Context::exit` writes):
* `2` (`Error`): the result is zeroed and its 32-bit `status_code` set to 1
  (`CallStatus::Failure`);
* `3` (`OutOfGas`): the result is zeroed and `status_code` set to 3.
In both `gas_left` (`result + 8`), `output_data` (`+ 0x18`) and `output_size`
(`+ 0x20`) are 0. These paths call nothing.

The success/revert path (through `copy_result_data`) is not proved.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem crf_head (oS o2 oZ : BitVec 12) (base res cx r13 r14 r15 st : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .LD .x14 .x11 oS, .ADDI .x13 .x0 o2, .ADDI .x15 .x10 oZ])
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ res) ** (.x11 ↦ᵣ cx) ** (.x13 ↦ᵣ r13) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) ** ((cx + signExtend12 oS) ↦ₘ st))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ res) ** (.x11 ↦ᵣ cx) ** (.x13 ↦ᵣ ((0 : Word) + signExtend12 o2)) **
       (.x14 ↦ᵣ st) ** (.x15 ↦ᵣ (res + signExtend12 oZ)) ** ((cx + signExtend12 oS) ↦ₘ st)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem crf_first (o0 o1 : BitVec 12) (base res r14 a : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .SD .x10 .x0 o0, .ADDI .x14 .x0 o1])
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ res) ** (.x14 ↦ᵣ r14) ** ((res + signExtend12 o0) ↦ₘ a))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ res) ** (.x14 ↦ᵣ ((0 : Word) + signExtend12 o1)) **
       ((res + signExtend12 o0) ↦ₘ 0)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem crf_zero (o1 o2 o3 o4 o5 o6 : BitVec 12) (base res a1 a2 a3 a4 a5 a6 : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base [
      .SD .x15 .x0 o1, .SD .x15 .x0 o2, .SD .x15 .x0 o3, .SD .x15 .x0 o4, .SD .x15 .x0 o5,
      .SD .x15 .x0 o6])
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ res) **
       ((res + signExtend12 o1) ↦ₘ a1) ** ((res + signExtend12 o2) ↦ₘ a2) **
       ((res + signExtend12 o3) ↦ₘ a3) ** ((res + signExtend12 o4) ↦ₘ a4) **
       ((res + signExtend12 o5) ↦ₘ a5) ** ((res + signExtend12 o6) ↦ₘ a6))
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ res) **
       ((res + signExtend12 o1) ↦ₘ 0) ** ((res + signExtend12 o2) ↦ₘ 0) **
       ((res + signExtend12 o3) ↦ₘ 0) ** ((res + signExtend12 o4) ↦ₘ 0) **
       ((res + signExtend12 o5) ↦ₘ 0) ** ((res + signExtend12 o6) ↦ₘ 0)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem crf_ret (oZ : BitVec 12) (base res r10 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x10 .x15 oZ])
      ((.x10 ↦ᵣ r10) ** (.x15 ↦ᵣ res))
      ((.x10 ↦ᵣ (res + signExtend12 oZ)) ** (.x15 ↦ᵣ res)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem crf_li10 (o : BitVec 12) (base r10 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x10 .x0 o])
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ r10))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 o))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem crf_sd0 (o : BitVec 12) (base res a : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.SD .x15 .x0 o])
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ res) ** ((res + signExtend12 o) ↦ₘ a))
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ res) ** ((res + signExtend12 o) ↦ₘ 0)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The common end of both failure paths, from `base + 260`: zero the fields
    at `+8 … +0x30`, the 32-bit field at `+0x38`, store the 32-bit status code
    `x14` at `+0`, return `res`. -/
theorem crf_tail (base ra res r10 code a1 a2 a3 a4 a5 a6 a7 : Word)
    (q0 q8 q10 q18 q20 q28 q30 q38 : Word)
    (h_q8 : res + signExtend12 0x008#12 = q8) (h_q10 : res + signExtend12 0x010#12 = q10)
    (h_q18 : res + signExtend12 0x018#12 = q18) (h_q20 : res + signExtend12 0x020#12 = q20)
    (h_q28 : res + signExtend12 0x028#12 = q28) (h_q30 : res + signExtend12 0x030#12 = q30)
    (h_q38 : alignToDword (res + signExtend12 0x038#12) = q38)
    (h_v38 : isValidMemAccess (res + signExtend12 0x038#12) = true)
    (h_q0 : alignToDword (res + signExtend12 0x000#12) = q0)
    (h_v0 : isValidMemAccess (res + signExtend12 0x000#12) = true) :
    cpsTripleWithin 10 (base + 260) ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_rt_Context_copy_to_result.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ r10) ** (.x14 ↦ᵣ code) ** (.x15 ↦ᵣ res) **
       (q0 ↦ₘ 0) ** (q8 ↦ₘ a1) ** (q10 ↦ₘ a2) ** (q18 ↦ₘ a3) ** (q20 ↦ₘ a4) ** (q28 ↦ₘ a5) **
       (q30 ↦ₘ a6) ** (q38 ↦ₘ a7))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ res) ** (.x14 ↦ᵣ code) ** (.x15 ↦ᵣ res) **
       (q0 ↦ₘ replaceWord32 0 ((byteOffset (res + signExtend12 0x000#12)) / 4) (code.truncate 32)) **
       (q8 ↦ₘ 0) ** (q10 ↦ₘ 0) ** (q18 ↦ₘ 0) ** (q20 ↦ₘ 0) ** (q28 ↦ₘ 0) ** (q30 ↦ₘ 0) **
       (q38 ↦ₘ replaceWord32 a7 ((byteOffset (res + signExtend12 0x038#12)) / 4)
          ((0 : Word).truncate 32))) := by
  have hz := crf_zero 0x008#12 0x010#12 0x018#12 0x020#12 0x028#12 0x030#12 (base + 260) res
    a1 a2 a3 a4 a5 a6
  rw [h_q8, h_q10, h_q18, h_q20, h_q28, h_q30] at hz
  have hs1 := sw_spec_gen_within .x15 .x0 res 0 0x038#12 (base + 284) q38 a7 h_q38 h_v38
  have hs2 := sw_spec_gen_within .x15 .x14 res code 0x000#12 (base + 288) q0 0 h_q0 h_v0
  have hr := crf_ret 0x000#12 (base + 292) res r10
  rw [add_se12_zero] at hr
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 296)
  have hz := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 260) Image.f_rt_Context_copy_to_result.prog _ 65 (by rfl) (by decide) (by decide) (by decide)) hz
  have hs1 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 71 (base + 284) (by decide) (by decide) (by rfl))) hs1
  have hs2 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 72 (base + 288) (by decide) (by decide) (by rfl))) hs2
  have hr := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 292) Image.f_rt_Context_copy_to_result.prog _ 73 (by rfl) (by decide) (by decide) (by decide)) hr
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 74 (base + 296) (by decide) (by decide) (by rfl))) hj
  runBlock hz hs1 hs2 hr hj


/-- `copy_to_result` when the context's status is 2 (`Error`): the result has
    32-bit status code 1 (`CallStatus::Failure`) and every other field 0. -/
theorem copy_to_result_error (base ra res cx r13 r14 r15 st a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (stcell q0 q8 q10 q18 q20 q28 q30 q38 : Word)
    (h_stcell : cx + signExtend12 0x0f8#12 = stcell)
    (h_q0s : res + signExtend12 0x000#12 = q0)
    (h_q8 : res + signExtend12 0x008#12 = q8) (h_q10 : res + signExtend12 0x010#12 = q10)
    (h_q18 : res + signExtend12 0x018#12 = q18) (h_q20 : res + signExtend12 0x020#12 = q20)
    (h_q28 : res + signExtend12 0x028#12 = q28) (h_q30 : res + signExtend12 0x030#12 = q30)
    (h_q38 : alignToDword (res + signExtend12 0x038#12) = q38)
    (h_v38 : isValidMemAccess (res + signExtend12 0x038#12) = true)
    (h_q0 : alignToDword (res + signExtend12 0x000#12) = q0)
    (h_v0 : isValidMemAccess (res + signExtend12 0x000#12) = true)
    (hst : st = 2) :
    cpsTripleWithin 16 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_rt_Context_copy_to_result.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ res) ** (.x11 ↦ᵣ cx) ** (.x13 ↦ᵣ r13) **
       (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) ** (stcell ↦ₘ st) **
       (q0 ↦ₘ a0) ** (q8 ↦ₘ a1) ** (q10 ↦ₘ a2) ** (q18 ↦ₘ a3) ** (q20 ↦ₘ a4) ** (q28 ↦ₘ a5) **
       (q30 ↦ₘ a6) ** (q38 ↦ₘ a7))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ res) ** (.x11 ↦ᵣ cx) **
       (.x13 ↦ᵣ ((0 : Word) + signExtend12 0x002#12)) ** (.x14 ↦ᵣ ((0 : Word) + signExtend12 0x001#12)) ** (.x15 ↦ᵣ res) **
       (stcell ↦ₘ st) **
       (q0 ↦ₘ replaceWord32 0 ((byteOffset (res + signExtend12 0x000#12)) / 4) (((0 : Word) + signExtend12 0x001#12).truncate 32)) **
       (q8 ↦ₘ 0) ** (q10 ↦ₘ 0) ** (q18 ↦ₘ 0) ** (q20 ↦ₘ 0) ** (q28 ↦ₘ 0) ** (q30 ↦ₘ 0) **
       (q38 ↦ₘ replaceWord32 a7 ((byteOffset (res + signExtend12 0x038#12)) / 4)
          ((0 : Word).truncate 32))) := by
  have hst' : st = (0 : Word) + signExtend12 0x002#12 := by rw [hst]; decide
  have h0 := crf_head 0x0f8#12 0x002#12 0x000#12 base res cx r13 r14 r15 st
  rw [h_stcell, add_se12_zero] at h0
  have hbeq := cpsBranchWithin_takenStripPure2
    (beq_spec_gen_within .x14 .x13 0x00f0#13 st ((0 : Word) + signExtend12 0x002#12) (base + 12))
    (fun hp hq => (pure_end2 hp hq) hst')
  have e : base + 12 + signExtend13 0x00f0#13 = base + 252 := by rv64_addr
  rw [e] at hbeq
  have h1 := crf_first 0x000#12 0x001#12 (base + 252) res st a0
  rw [h_q0s] at h1
  have ht := crf_tail base ra res res ((0 : Word) + signExtend12 0x001#12) a1 a2 a3 a4 a5 a6 a7 q0 q8 q10 q18 q20 q28 q30 q38 h_q8 h_q10 h_q18 h_q20 h_q28 h_q30 h_q38 h_v38 h_q0 h_v0
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_rt_Context_copy_to_result.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hbeq
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 252) Image.f_rt_Context_copy_to_result.prog _ 63 (by rfl) (by decide) (by decide) (by decide)) h1
  runBlock h0 hbeq h1 ht

/-- `copy_to_result` when the context's status is 3 (`OutOfGas`): the result
    has 32-bit status code 3 (`CallStatus::OutOfGas`) and every other field 0. -/
theorem copy_to_result_oog (base ra res cx r13 r14 r15 st a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (stcell q0 q8 q10 q18 q20 q28 q30 q38 : Word)
    (h_stcell : cx + signExtend12 0x0f8#12 = stcell)
    (h_q0s : res + signExtend12 0x000#12 = q0)
    (h_q8 : res + signExtend12 0x008#12 = q8) (h_q10 : res + signExtend12 0x010#12 = q10)
    (h_q18 : res + signExtend12 0x018#12 = q18) (h_q20 : res + signExtend12 0x020#12 = q20)
    (h_q28 : res + signExtend12 0x028#12 = q28) (h_q30 : res + signExtend12 0x030#12 = q30)
    (h_q38 : alignToDword (res + signExtend12 0x038#12) = q38)
    (h_v38 : isValidMemAccess (res + signExtend12 0x038#12) = true)
    (h_q0 : alignToDword (res + signExtend12 0x000#12) = q0)
    (h_v0 : isValidMemAccess (res + signExtend12 0x000#12) = true)
    (hst : st = 3) :
    cpsTripleWithin 19 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_rt_Context_copy_to_result.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ res) ** (.x11 ↦ᵣ cx) ** (.x13 ↦ᵣ r13) **
       (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) ** (stcell ↦ₘ st) **
       (q0 ↦ₘ a0) ** (q8 ↦ₘ a1) ** (q10 ↦ₘ a2) ** (q18 ↦ₘ a3) ** (q20 ↦ₘ a4) ** (q28 ↦ₘ a5) **
       (q30 ↦ₘ a6) ** (q38 ↦ₘ a7))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ res) ** (.x11 ↦ᵣ cx) **
       (.x13 ↦ᵣ ((0 : Word) + signExtend12 0x002#12)) ** (.x14 ↦ᵣ st) ** (.x15 ↦ᵣ res) **
       (stcell ↦ₘ st) **
       (q0 ↦ₘ replaceWord32 0 ((byteOffset (res + signExtend12 0x000#12)) / 4) (st.truncate 32)) **
       (q8 ↦ₘ 0) ** (q10 ↦ₘ 0) ** (q18 ↦ₘ 0) ** (q20 ↦ₘ 0) ** (q28 ↦ₘ 0) ** (q30 ↦ₘ 0) **
       (q38 ↦ₘ replaceWord32 a7 ((byteOffset (res + signExtend12 0x038#12)) / 4)
          ((0 : Word).truncate 32))) := by
  have hst2 : st ≠ (0 : Word) + signExtend12 0x002#12 := by rw [hst]; decide
  have hst3 : st = (0 : Word) + signExtend12 0x003#12 := by rw [hst]; decide
  have h0 := crf_head 0x0f8#12 0x002#12 0x000#12 base res cx r13 r14 r15 st
  rw [h_stcell, add_se12_zero] at h0
  have hbeq := cpsBranchWithin_ntakenStripPure2
    (beq_spec_gen_within .x14 .x13 0x00f0#13 st ((0 : Word) + signExtend12 0x002#12) (base + 12))
    (fun hp hq => hst2 (pure_end2 hp hq))
  have hli := crf_li10 0x003#12 (base + 16) res
  have hbeq2 := cpsBranchWithin_takenStripPure2
    (beq_spec_gen_within .x14 .x10 0x0118#13 st ((0 : Word) + signExtend12 0x003#12) (base + 20))
    (fun hp hq => (pure_end2 hp hq) hst3)
  have e : base + 20 + signExtend13 0x0118#13 = base + 300 := by rv64_addr
  rw [e] at hbeq2
  have hsd := crf_sd0 0x000#12 (base + 300) res a0
  rw [h_q0s] at hsd
  have hj := jal_x0_spec_gen_within 0x1fffd4#21 (base + 304)
  have e2 : base + 304 + signExtend21 0x1fffd4#21 = base + 260 := by rv64_addr
  rw [e2] at hj
  have ht := crf_tail base ra res ((0 : Word) + signExtend12 0x003#12) st a1 a2 a3 a4 a5 a6 a7 q0 q8 q10 q18 q20 q28 q30 q38 h_q8 h_q10 h_q18 h_q20 h_q28 h_q30 h_q38 h_v38 h_q0 h_v0
  have h0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base base Image.f_rt_Context_copy_to_result.prog _ 0 (by simp) (by decide) (by decide) (by decide)) h0
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 3 (base + 12) (by decide) (by decide) (by rfl))) hbeq
  have hli := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_rt_Context_copy_to_result.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) hli
  have hbeq2 := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 5 (base + 20) (by decide) (by decide) (by rfl))) hbeq2
  have hsd := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 300) Image.f_rt_Context_copy_to_result.prog _ 75 (by rfl) (by decide) (by decide) (by decide)) hsd
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_rt_Context_copy_to_result.prog 76 (base + 304) (by decide) (by decide) (by rfl))) hj
  runBlock h0 hbeq hli hbeq2 hsd hj ht

end PureInterp.Entry
