import PureInterp.Entry.Basic

/-!
# `monad_pure_execute`: writing the output struct

The 13 instructions of `monad_pure_execute` between the return of
`copy_to_result` (`bx + 188`) and the first cleanup call (`bx + 240`):
read the 32-bit `status_code` of the `vm::Result` at `sp + 0x60`, map it
(`0 ↦ 0`, `2 ↦ 1`, anything else `↦ 2`), and store `status`, `gas_left`,
`output`, `output_size` into the `monad_pure_output` at `s1`.

`sc` is the sign-extended status code. `out_success` is the case `sc = 0`,
`out_failure` the cases `sc = 1` (`CallStatus::Failure`) and `sc = 3`
(`CallStatus::OutOfGas`), `out_revert` the case `sc = 2`.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem out_li15 (o : BitVec 12) (base r15 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADDI .x15 .x0 o])
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ r15))
      ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ ((0 : Word) + signExtend12 o))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem out_map (oM o1 : BitVec 12) (base sc r15 : Word) :
    cpsTripleWithin 3 base (base + 12) (CodeReq.ofProg base [
      .ADDI .x14 .x14 oM, .SLTU .x15 .x0 .x14, .ADDI .x15 .x15 o1])
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ sc) ** (.x15 ↦ᵣ r15))
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ (sc + signExtend12 oM)) **
       (.x15 ↦ᵣ ((if BitVec.ult (0 : Word) (sc + signExtend12 oM) then (1 : Word) else 0) +
          signExtend12 o1))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem out_store (o78 o68 o0 o80 o10 o8 o18 : BitVec 12)
    (base sp out r10 r14 stv od gl os b0 b1 b2 b3 : Word) :
    cpsTripleWithin 7 base (base + 28) (CodeReq.ofProg base [
      .LD .x10 .x2 o78, .LD .x14 .x2 o68, .SD .x9 .x15 o0, .LD .x15 .x2 o80,
      .SD .x9 .x10 o10, .SD .x9 .x14 o8, .SD .x9 .x15 o18])
      ((.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ r10) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ stv) **
       ((sp + signExtend12 o78) ↦ₘ od) ** ((sp + signExtend12 o68) ↦ₘ gl) **
       ((sp + signExtend12 o80) ↦ₘ os) **
       ((out + signExtend12 o0) ↦ₘ b0) ** ((out + signExtend12 o8) ↦ₘ b1) **
       ((out + signExtend12 o10) ↦ₘ b2) ** ((out + signExtend12 o18) ↦ₘ b3))
      ((.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ od) ** (.x14 ↦ᵣ gl) ** (.x15 ↦ᵣ os) **
       ((sp + signExtend12 o78) ↦ₘ od) ** ((sp + signExtend12 o68) ↦ₘ gl) **
       ((sp + signExtend12 o80) ↦ₘ os) **
       ((out + signExtend12 o0) ↦ₘ stv) ** ((out + signExtend12 o8) ↦ₘ gl) **
       ((out + signExtend12 o10) ↦ₘ od) ** ((out + signExtend12 o18) ↦ₘ os)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- Status code 0: `out->status = 0`; `gas_left`, `output`, `output_size`
    copied from the result (`gl`, `od`, `os`). -/
theorem out_success (bx sp out r10 r14 r15 w60 sc od gl os b0 b1 b2 b3 : Word)
    (c60 k78 k68 k80 u0 u8 u10 u18 : Word)
    (h_c60 : alignToDword (sp + signExtend12 0x060#12) = c60)
    (h_v60 : isValidMemAccess (sp + signExtend12 0x060#12) = true)
    (h_sc : (extractWord32 w60 ((byteOffset (sp + signExtend12 0x060#12)) / 4)).signExtend 64 = sc)
    (h_k78 : sp + signExtend12 0x078#12 = k78) (h_k68 : sp + signExtend12 0x068#12 = k68)
    (h_k80 : sp + signExtend12 0x080#12 = k80)
    (h_u0 : out + signExtend12 0x000#12 = u0) (h_u8 : out + signExtend12 0x008#12 = u8)
    (h_u10 : out + signExtend12 0x010#12 = u10) (h_u18 : out + signExtend12 0x018#12 = u18)
    (hsc : sc = 0) :
    cpsTripleWithin 10 (bx + 188) (bx + 240)
      (CodeReq.ofProg bx Image.f_monad_pure_execute.prog)
      ((.x0 ↦ᵣ 0) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ r10) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) ** (c60 ↦ₘ w60) ** (k78 ↦ₘ od) ** (k68 ↦ₘ gl) ** (k80 ↦ₘ os) **
       (u0 ↦ₘ b0) ** (u8 ↦ₘ b1) ** (u10 ↦ₘ b2) ** (u18 ↦ₘ b3))
      ((.x0 ↦ᵣ 0) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ od) ** (.x14 ↦ᵣ gl) **
       (.x15 ↦ᵣ os) ** (c60 ↦ₘ w60) ** (k78 ↦ₘ od) ** (k68 ↦ₘ gl) ** (k80 ↦ₘ os) **
       (u0 ↦ₘ 0) ** (u8 ↦ₘ gl) ** (u10 ↦ₘ od) ** (u18 ↦ₘ os)) := by
  have hl := lw_spec_gen_within .x14 .x2 sp r14 0x060#12 (bx + 188) c60 w60 (by decide) h_c60 h_v60
  rw [h_sc] at hl
  have h1 := out_li15 0x000#12 (bx + 192) r15
  rw [add_se12_zero] at h1
  have hbeq := cpsBranchWithin_takenStripPure2
    (beq_spec_gen_within .x14 .x0 0x0010#13 sc 0 (bx + 196))
    (fun hp hq => (pure_end2 hp hq) hsc)
  have e : bx + 196 + signExtend13 0x0010#13 = bx + 212 := by rv64_addr
  rw [e] at hbeq
  have h2 := out_store 0x078#12 0x068#12 0x000#12 0x080#12 0x010#12 0x008#12 0x018#12
    (bx + 212) sp out r10 sc 0 od gl os b0 b1 b2 b3
  rw [h_k78, h_k68, h_k80, h_u0, h_u8, h_u10, h_u18] at h2
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bx Image.f_monad_pure_execute.prog 47 (bx + 188) (by decide) (by decide) (by rfl))) hl
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bx (bx + 192) Image.f_monad_pure_execute.prog _ 48 (by rfl) (by decide) (by decide) (by decide)) h1
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bx Image.f_monad_pure_execute.prog 49 (bx + 196) (by decide) (by decide) (by rfl))) hbeq
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bx (bx + 212) Image.f_monad_pure_execute.prog _ 53 (by rfl) (by decide) (by decide) (by decide)) h2
  runBlock hl h1 hbeq h2

/-- The mapped status for a non-zero status code. -/
def mapStatus (sc : Word) : Word :=
  (if BitVec.ult (0 : Word) (sc + signExtend12 0xffe#12) then (1 : Word) else 0) +
    signExtend12 0x001#12

theorem mapStatus_1 : mapStatus 1 = 2 := by decide
theorem mapStatus_2 : mapStatus 2 = 1 := by decide
theorem mapStatus_3 : mapStatus 3 = 2 := by decide

/-- Non-zero status code: `out->status = mapStatus sc`. -/
theorem out_nonzero (bx sp out r10 r14 r15 w60 sc od gl os b0 b1 b2 b3 : Word)
    (c60 k78 k68 k80 u0 u8 u10 u18 : Word)
    (h_c60 : alignToDword (sp + signExtend12 0x060#12) = c60)
    (h_v60 : isValidMemAccess (sp + signExtend12 0x060#12) = true)
    (h_sc : (extractWord32 w60 ((byteOffset (sp + signExtend12 0x060#12)) / 4)).signExtend 64 = sc)
    (h_k78 : sp + signExtend12 0x078#12 = k78) (h_k68 : sp + signExtend12 0x068#12 = k68)
    (h_k80 : sp + signExtend12 0x080#12 = k80)
    (h_u0 : out + signExtend12 0x000#12 = u0) (h_u8 : out + signExtend12 0x008#12 = u8)
    (h_u10 : out + signExtend12 0x010#12 = u10) (h_u18 : out + signExtend12 0x018#12 = u18)
    (hsc : sc ≠ 0) :
    cpsTripleWithin 13 (bx + 188) (bx + 240)
      (CodeReq.ofProg bx Image.f_monad_pure_execute.prog)
      ((.x0 ↦ᵣ 0) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ r10) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) ** (c60 ↦ₘ w60) ** (k78 ↦ₘ od) ** (k68 ↦ₘ gl) ** (k80 ↦ₘ os) **
       (u0 ↦ₘ b0) ** (u8 ↦ₘ b1) ** (u10 ↦ₘ b2) ** (u18 ↦ₘ b3))
      ((.x0 ↦ᵣ 0) ** (.x2 ↦ᵣ sp) ** (.x9 ↦ᵣ out) ** (.x10 ↦ᵣ od) ** (.x14 ↦ᵣ gl) **
       (.x15 ↦ᵣ os) ** (c60 ↦ₘ w60) ** (k78 ↦ₘ od) ** (k68 ↦ₘ gl) ** (k80 ↦ₘ os) **
       (u0 ↦ₘ mapStatus sc) ** (u8 ↦ₘ gl) ** (u10 ↦ₘ od) ** (u18 ↦ₘ os)) := by
  have hl := lw_spec_gen_within .x14 .x2 sp r14 0x060#12 (bx + 188) c60 w60 (by decide) h_c60 h_v60
  rw [h_sc] at hl
  have h1 := out_li15 0x000#12 (bx + 192) r15
  rw [add_se12_zero] at h1
  have hbeq := cpsBranchWithin_ntakenStripPure2
    (beq_spec_gen_within .x14 .x0 0x0010#13 sc 0 (bx + 196))
    (fun hp hq => hsc (pure_end2 hp hq))
  have hm := out_map 0xffe#12 0x001#12 (bx + 200) sc 0
  rw [show (if BitVec.ult (0 : Word) (sc + signExtend12 0xffe#12) then (1 : Word) else 0) +
    signExtend12 0x001#12 = mapStatus sc from rfl] at hm
  have h2 := out_store 0x078#12 0x068#12 0x000#12 0x080#12 0x010#12 0x008#12 0x018#12
    (bx + 212) sp out r10 (sc + signExtend12 0xffe#12) (mapStatus sc) od gl os b0 b1 b2 b3
  rw [h_k78, h_k68, h_k80, h_u0, h_u8, h_u10, h_u18] at h2
  have hl := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bx Image.f_monad_pure_execute.prog 47 (bx + 188) (by decide) (by decide) (by rfl))) hl
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bx (bx + 192) Image.f_monad_pure_execute.prog _ 48 (by rfl) (by decide) (by decide) (by decide)) h1
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr bx Image.f_monad_pure_execute.prog 49 (bx + 196) (by decide) (by decide) (by rfl))) hbeq
  have hm := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bx (bx + 200) Image.f_monad_pure_execute.prog _ 50 (by rfl) (by decide) (by decide) (by decide)) hm
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub bx (bx + 212) Image.f_monad_pure_execute.prog _ 53 (by rfl) (by decide) (by decide) (by decide)) h2
  runBlock hl h1 hbeq hm h2

end PureInterp.Entry
