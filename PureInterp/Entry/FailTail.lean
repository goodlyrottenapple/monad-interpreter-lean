import PureInterp.Entry.CopyResultFail
import PureInterp.Entry.OutStruct

/-!
# The failure tail of `monad_pure_execute`

From the return of `trampoline` (`bx + 176`) through `copy_to_result` to the
last store into the output struct (`bx + 240`), when the interpreter halted
with context status 2 (`Error`) or 3 (`OutOfGas`): the output struct receives
`status = 2`, `gas_left = 0`, `output = 0`, `output_size = 0`.

Here `sp` is `monad_pure_execute`'s frame pointer, `cx = sp + 0x160` the
runtime context (so `stcell = cx + 0xf8` is `Machine.exitFrame`'s
`E.ctx + 248`), `res = sp + 0x60` the `vm::Result`, `out` (`s1`) the
`monad_pure_output`.

Not covered: the cleanup after `bx + 240` (`free`, `~Intercode`, the frame
pop and return), and the success/revert paths.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem ft_args (o1 o2 : BitVec 12) (base sp r10 r11 : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [
      .ADDI .x11 .x2 o1, .ADDI .x10 .x2 o2])
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11))
      ((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (sp + signExtend12 o2)) ** (.x11 ↦ᵣ (sp + signExtend12 o1))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem ew_same (w : Word) (p : Nat) (v : BitVec 32) (hp : p < 2) :
    extractWord32 (replaceWord32 w p v) p = v :=
  extractWord32_replaceWord32_same w ⟨p, hp⟩ v

theorem off_add (sp : Word) (a b c : BitVec 12)
    (h : signExtend12 a + signExtend12 b = signExtend12 c) :
    sp + signExtend12 a + signExtend12 b = sp + signExtend12 c := by
  rw [BitVec.add_assoc, h]

/-- Context status 2 (`Error`, e.g. the invalid handler or a stack error). -/
theorem fail_tail_error (cr : CodeReq) (bx bq sp out res cx r1 r10 r11 r13 r14 r15 : Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : Word)
    (stcell q0 q8 q10 q18 q20 q28 q30 q38 u0 u8 u10 u18 : Word)
    (hcx : ∀ a i, CodeReq.ofProg bx Image.f_monad_pure_execute.prog a = some i → cr a = some i)
    (hcq : ∀ a i, CodeReq.ofProg bq Image.f_rt_Context_copy_to_result.prog a = some i → cr a = some i)
    (h_bq : bx + 184 + signExtend21 0x000a10#21 = bq)
    (h_rx : (bx + 184 + 4 + signExtend12 0x000#12) &&& ~~~1 = bx + 188)
    (h_res : sp + signExtend12 0x060#12 = res)
    (h_cx : sp + signExtend12 0x160#12 = cx)
    (h_stcell : cx + signExtend12 0x0f8#12 = stcell)
    (h_q0s : res + signExtend12 0x000#12 = q0)
    (h_q8 : res + signExtend12 0x008#12 = q8) (h_q10 : res + signExtend12 0x010#12 = q10)
    (h_q18 : res + signExtend12 0x018#12 = q18) (h_q20 : res + signExtend12 0x020#12 = q20)
    (h_q28 : res + signExtend12 0x028#12 = q28) (h_q30 : res + signExtend12 0x030#12 = q30)
    (h_q38 : alignToDword (res + signExtend12 0x038#12) = q38)
    (h_v38 : isValidMemAccess (res + signExtend12 0x038#12) = true)
    (h_q0 : alignToDword (res + signExtend12 0x000#12) = q0)
    (h_v0 : isValidMemAccess (res + signExtend12 0x000#12) = true)
    (h_u0 : out + signExtend12 0x000#12 = u0) (h_u8 : out + signExtend12 0x008#12 = u8)
    (h_u10 : out + signExtend12 0x010#12 = u10) (h_u18 : out + signExtend12 0x018#12 = u18) :
    cpsTripleWithin 32 (bx + 176) (bx + 240) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ r10) **
       (.x11 ↦ᵣ r11) ** (.x13 ↦ᵣ r13) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (stcell ↦ₘ 2) **
       (q0 ↦ₘ a0) ** (q8 ↦ₘ a1) ** (q10 ↦ₘ a2) ** (q18 ↦ₘ a3) ** (q20 ↦ₘ a4) ** (q28 ↦ₘ a5) **
       (q30 ↦ₘ a6) ** (q38 ↦ₘ a7) **
       (u0 ↦ₘ b0) ** (u8 ↦ₘ b1) ** (u10 ↦ₘ b2) ** (u18 ↦ₘ b3))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bx + 184 + 4)) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ 0) **
       (.x11 ↦ᵣ cx) ** (.x13 ↦ᵣ ((0 : Word) + signExtend12 0x002#12)) ** (.x14 ↦ᵣ 0) **
       (.x15 ↦ᵣ 0) ** (stcell ↦ₘ 2) **
       (q0 ↦ₘ replaceWord32 0 ((byteOffset res) / 4) (((0 : Word) + signExtend12 0x001#12).truncate 32)) **
       (q8 ↦ₘ 0) ** (q10 ↦ₘ 0) ** (q18 ↦ₘ 0) ** (q20 ↦ₘ 0) ** (q28 ↦ₘ 0) ** (q30 ↦ₘ 0) **
       (q38 ↦ₘ replaceWord32 a7 ((byteOffset (res + signExtend12 0x038#12)) / 4)
          ((0 : Word).truncate 32)) **
       (u0 ↦ₘ 2) ** (u8 ↦ₘ 0) ** (u10 ↦ₘ 0) ** (u18 ↦ₘ 0)) := by
  have ha := ft_args 0x160#12 0x060#12 (bx + 176) sp r10 r11
  rw [h_res, h_cx] at ha
  have hj := jal_spec_within .x1 r1 0x000a10#21 (bx + 184) (by decide)
  rw [h_bq] at hj
  have hc := copy_to_result_error bq (bx + 184 + 4) res cx r13 r14 r15 (2) a0 a1 a2 a3 a4 a5 a6 a7
    stcell q0 q8 q10 q18 q20 q28 q30 q38 h_stcell h_q0s h_q8 h_q10 h_q18 h_q20 h_q28 h_q30
    h_q38 h_v38 h_q0 h_v0 rfl
  rw [h_rx, add_se12_zero] at hc
  have hsc : (extractWord32 (replaceWord32 0 ((byteOffset res) / 4) (((0 : Word) + signExtend12 0x001#12).truncate 32))
      ((byteOffset (sp + signExtend12 0x060#12)) / 4)).signExtend 64 = ((0 : Word) + signExtend12 0x001#12) := by
    rw [h_res, ew_same _ _ _ (by have := @byteOffset_lt_8 res; omega)]
    decide
  have ho := out_nonzero bx sp out res ((0 : Word) + signExtend12 0x001#12) res
    (replaceWord32 0 ((byteOffset res) / 4) (((0 : Word) + signExtend12 0x001#12).truncate 32)) ((0 : Word) + signExtend12 0x001#12) 0 0 0 b0 b1 b2 b3
    q0 q18 q8 q20 u0 u8 u10 u18
    (by rw [h_res]; rw [add_se12_zero] at h_q0; exact h_q0)
    (by rw [h_res]; rw [add_se12_zero] at h_v0; exact h_v0)
    hsc
    (by rw [← h_q18, ← h_res]; exact (off_add sp _ _ _ (by decide)).symm)
    (by rw [← h_q8, ← h_res]; exact (off_add sp _ _ _ (by decide)).symm)
    (by rw [← h_q20, ← h_res]; exact (off_add sp _ _ _ (by decide)).symm)
    h_u0 h_u8 h_u10 h_u18 (by decide)
  rw [show mapStatus ((0 : Word) + signExtend12 0x001#12) = 2 from by decide] at ho
  have ha := cpsTripleWithin_extend_code (fun a i h => hcx a i
    (CodeReq.ofProg_mono_sub bx (bx + 176) Image.f_monad_pure_execute.prog _ 44 (by rfl) (by decide) (by decide) (by decide) a i h)) ha
  have hj := cpsTripleWithin_extend_code (fun a i h => hcx a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bx Image.f_monad_pure_execute.prog 46 (bx + 184) (by decide) (by decide) (by rfl)) a i h)) hj
  have hc := cpsTripleWithin_extend_code hcq hc
  have ho := cpsTripleWithin_extend_code hcx ho
  runBlock ha hj hc ho

/-- Context status 3 (`OutOfGas`). -/
theorem fail_tail_oog (cr : CodeReq) (bx bq sp out res cx r1 r10 r11 r13 r14 r15 : Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : Word)
    (stcell q0 q8 q10 q18 q20 q28 q30 q38 u0 u8 u10 u18 : Word)
    (hcx : ∀ a i, CodeReq.ofProg bx Image.f_monad_pure_execute.prog a = some i → cr a = some i)
    (hcq : ∀ a i, CodeReq.ofProg bq Image.f_rt_Context_copy_to_result.prog a = some i → cr a = some i)
    (h_bq : bx + 184 + signExtend21 0x000a10#21 = bq)
    (h_rx : (bx + 184 + 4 + signExtend12 0x000#12) &&& ~~~1 = bx + 188)
    (h_res : sp + signExtend12 0x060#12 = res)
    (h_cx : sp + signExtend12 0x160#12 = cx)
    (h_stcell : cx + signExtend12 0x0f8#12 = stcell)
    (h_q0s : res + signExtend12 0x000#12 = q0)
    (h_q8 : res + signExtend12 0x008#12 = q8) (h_q10 : res + signExtend12 0x010#12 = q10)
    (h_q18 : res + signExtend12 0x018#12 = q18) (h_q20 : res + signExtend12 0x020#12 = q20)
    (h_q28 : res + signExtend12 0x028#12 = q28) (h_q30 : res + signExtend12 0x030#12 = q30)
    (h_q38 : alignToDword (res + signExtend12 0x038#12) = q38)
    (h_v38 : isValidMemAccess (res + signExtend12 0x038#12) = true)
    (h_q0 : alignToDword (res + signExtend12 0x000#12) = q0)
    (h_v0 : isValidMemAccess (res + signExtend12 0x000#12) = true)
    (h_u0 : out + signExtend12 0x000#12 = u0) (h_u8 : out + signExtend12 0x008#12 = u8)
    (h_u10 : out + signExtend12 0x010#12 = u10) (h_u18 : out + signExtend12 0x018#12 = u18) :
    cpsTripleWithin 35 (bx + 176) (bx + 240) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ r10) **
       (.x11 ↦ᵣ r11) ** (.x13 ↦ᵣ r13) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (stcell ↦ₘ 3) **
       (q0 ↦ₘ a0) ** (q8 ↦ₘ a1) ** (q10 ↦ₘ a2) ** (q18 ↦ₘ a3) ** (q20 ↦ₘ a4) ** (q28 ↦ₘ a5) **
       (q30 ↦ₘ a6) ** (q38 ↦ₘ a7) **
       (u0 ↦ₘ b0) ** (u8 ↦ₘ b1) ** (u10 ↦ₘ b2) ** (u18 ↦ₘ b3))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bx + 184 + 4)) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ 0) **
       (.x11 ↦ᵣ cx) ** (.x13 ↦ᵣ ((0 : Word) + signExtend12 0x002#12)) ** (.x14 ↦ᵣ 0) **
       (.x15 ↦ᵣ 0) ** (stcell ↦ₘ 3) **
       (q0 ↦ₘ replaceWord32 0 ((byteOffset res) / 4) (((3 : Word)).truncate 32)) **
       (q8 ↦ₘ 0) ** (q10 ↦ₘ 0) ** (q18 ↦ₘ 0) ** (q20 ↦ₘ 0) ** (q28 ↦ₘ 0) ** (q30 ↦ₘ 0) **
       (q38 ↦ₘ replaceWord32 a7 ((byteOffset (res + signExtend12 0x038#12)) / 4)
          ((0 : Word).truncate 32)) **
       (u0 ↦ₘ 2) ** (u8 ↦ₘ 0) ** (u10 ↦ₘ 0) ** (u18 ↦ₘ 0)) := by
  have ha := ft_args 0x160#12 0x060#12 (bx + 176) sp r10 r11
  rw [h_res, h_cx] at ha
  have hj := jal_spec_within .x1 r1 0x000a10#21 (bx + 184) (by decide)
  rw [h_bq] at hj
  have hc := copy_to_result_oog bq (bx + 184 + 4) res cx r13 r14 r15 (3) a0 a1 a2 a3 a4 a5 a6 a7
    stcell q0 q8 q10 q18 q20 q28 q30 q38 h_stcell h_q0s h_q8 h_q10 h_q18 h_q20 h_q28 h_q30
    h_q38 h_v38 h_q0 h_v0 rfl
  rw [h_rx, add_se12_zero] at hc
  have hsc : (extractWord32 (replaceWord32 0 ((byteOffset res) / 4) (((3 : Word)).truncate 32))
      ((byteOffset (sp + signExtend12 0x060#12)) / 4)).signExtend 64 = ((3 : Word)) := by
    rw [h_res, ew_same _ _ _ (by have := @byteOffset_lt_8 res; omega)]
    decide
  have ho := out_nonzero bx sp out res ((3 : Word)) res
    (replaceWord32 0 ((byteOffset res) / 4) (((3 : Word)).truncate 32)) ((3 : Word)) 0 0 0 b0 b1 b2 b3
    q0 q18 q8 q20 u0 u8 u10 u18
    (by rw [h_res]; rw [add_se12_zero] at h_q0; exact h_q0)
    (by rw [h_res]; rw [add_se12_zero] at h_v0; exact h_v0)
    hsc
    (by rw [← h_q18, ← h_res]; exact (off_add sp _ _ _ (by decide)).symm)
    (by rw [← h_q8, ← h_res]; exact (off_add sp _ _ _ (by decide)).symm)
    (by rw [← h_q20, ← h_res]; exact (off_add sp _ _ _ (by decide)).symm)
    h_u0 h_u8 h_u10 h_u18 (by decide)
  rw [show mapStatus ((3 : Word)) = 2 from by decide] at ho
  have ha := cpsTripleWithin_extend_code (fun a i h => hcx a i
    (CodeReq.ofProg_mono_sub bx (bx + 176) Image.f_monad_pure_execute.prog _ 44 (by rfl) (by decide) (by decide) (by decide) a i h)) ha
  have hj := cpsTripleWithin_extend_code (fun a i h => hcx a i (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bx Image.f_monad_pure_execute.prog 46 (bx + 184) (by decide) (by decide) (by rfl)) a i h)) hj
  have hc := cpsTripleWithin_extend_code hcq hc
  have ho := cpsTripleWithin_extend_code hcx ho
  runBlock ha hj hc ho

end PureInterp.Entry
