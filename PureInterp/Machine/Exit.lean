import PureInterp.Machine.Lemmas
import PureInterp.Handlers.Exit

/-!
# Leaving the interpreter

Every halting path ends by calling `runtime::Context::exit(status)`, which
stores the status in the context and `longjmp`s to the buffer the trampoline
set up. `exit_chain` is that tail, from the entry of `Context::exit` to the
`setjmp` return site, stated once for all paths.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

theorem se_lit_8 : signExtend12 0x008#12 = (8 : Word) := by decide
theorem se_lit_16 : signExtend12 0x010#12 = (16 : Word) := by decide
theorem se_lit_24 : signExtend12 0x018#12 = (24 : Word) := by decide
theorem se_lit_32 : signExtend12 0x020#12 = (32 : Word) := by decide
theorem se_lit_40 : signExtend12 0x028#12 = (40 : Word) := by decide
theorem se_lit_48 : signExtend12 0x030#12 = (48 : Word) := by decide
theorem se_lit_56 : signExtend12 0x038#12 = (56 : Word) := by decide
theorem se_lit_64 : signExtend12 0x040#12 = (64 : Word) := by decide
theorem se_lit_72 : signExtend12 0x048#12 = (72 : Word) := by decide
theorem se_lit_80 : signExtend12 0x050#12 = (80 : Word) := by decide
theorem se_lit_88 : signExtend12 0x058#12 = (88 : Word) := by decide
theorem se_lit_96 : signExtend12 0x060#12 = (96 : Word) := by decide
theorem se_lit_104 : signExtend12 0x068#12 = (104 : Word) := by decide
theorem se_lit_248 : signExtend12 0x0f8#12 = (248 : Word) := by decide
theorem se_lit_304 : signExtend12 0x130#12 = (304 : Word) := by decide

theorem a0_one : ((if BitVec.ult ((0 : Word) + signExtend12 0x001#12) (signExtend12 0x001#12)
    then (1 : Word) else 0) + ((0 : Word) + signExtend12 0x001#12)) = 1 := by decide

/-- From the entry of `Context::exit` with the status in `a1`, to the address
    saved in the jump buffer: the status is in the context, `ra`, `s0`–`s11`
    and `sp` come from the buffer, and `a0 = 1`. -/
theorem exit_chain (cr : CodeReq) (be bl ctx sp ra st r15 jb slot st0 scell : Word)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Word)
    (hce : ∀ a i, CodeReq.ofProg be Image.f_rt_Context_exit.prog a = some i → cr a = some i)
    (hcl : ∀ a i, CodeReq.ofProg bl Image.f_longjmp.prog a = some i → cr a = some i)
    (h_bl : be + 24 + signExtend21 0x000044#21 = bl)
    (h_scell : sp + signExtend12 0xff0#12 + signExtend12 0x008#12 = scell) :
    cpsTripleWithin 24 be ((v0 + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ st) **
       (.x15 ↦ᵣ r15) ** (.x8 ↦ᵣ c0) ** (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) ** (.x19 ↦ᵣ c3) **
       (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) ** (.x22 ↦ᵣ c6) ** (.x23 ↦ᵣ c7) ** (.x24 ↦ᵣ c8) **
       (.x25 ↦ᵣ c9) ** (.x26 ↦ᵣ c10) ** (.x27 ↦ᵣ c11) ** ((ctx + 304) ↦ₘ jb) ** (scell ↦ₘ slot) **
       ((ctx + 248) ↦ₘ st0) ** (jb ↦ₘ v0) ** ((jb + 8) ↦ₘ v1) ** ((jb + 16) ↦ₘ v2) **
       ((jb + 24) ↦ₘ v3) ** ((jb + 32) ↦ₘ v4) ** ((jb + 40) ↦ₘ v5) ** ((jb + 48) ↦ₘ v6) **
       ((jb + 56) ↦ₘ v7) ** ((jb + 64) ↦ₘ v8) ** ((jb + 72) ↦ₘ v9) ** ((jb + 80) ↦ₘ v10) **
       ((jb + 88) ↦ₘ v11) ** ((jb + 96) ↦ₘ v12) ** ((jb + 104) ↦ₘ v13))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ v0) ** (.x2 ↦ᵣ v13) ** (.x10 ↦ᵣ 1) **
       (.x11 ↦ᵣ ((0 : Word) + signExtend12 0x001#12)) ** (.x15 ↦ᵣ ctx) ** (.x8 ↦ᵣ v1) **
       (.x9 ↦ᵣ v2) ** (.x18 ↦ᵣ v3) ** (.x19 ↦ᵣ v4) ** (.x20 ↦ᵣ v5) ** (.x21 ↦ᵣ v6) **
       (.x22 ↦ᵣ v7) ** (.x23 ↦ᵣ v8) ** (.x24 ↦ᵣ v9) ** (.x25 ↦ᵣ v10) ** (.x26 ↦ᵣ v11) **
       (.x27 ↦ᵣ v12) ** ((ctx + 304) ↦ₘ jb) ** (scell ↦ₘ ra) ** ((ctx + 248) ↦ₘ st) **
       (jb ↦ₘ v0) ** ((jb + 8) ↦ₘ v1) ** ((jb + 16) ↦ₘ v2) ** ((jb + 24) ↦ₘ v3) **
       ((jb + 32) ↦ₘ v4) ** ((jb + 40) ↦ₘ v5) ** ((jb + 48) ↦ₘ v6) ** ((jb + 56) ↦ₘ v7) **
       ((jb + 64) ↦ₘ v8) ** ((jb + 72) ↦ₘ v9) ** ((jb + 80) ↦ₘ v10) ** ((jb + 88) ↦ₘ v11) **
       ((jb + 96) ↦ₘ v12) ** ((jb + 104) ↦ₘ v13)) := by
  have h_j : ctx + signExtend12 0x130#12 = ctx + 304 := by rw [se_lit_304]
  have h_s : ctx + signExtend12 0x000#12 + signExtend12 0x0f8#12 = ctx + 248 := by
    have z : ctx + (0 : Word) = ctx := BitVec.add_zero ctx
    rw [se_000, z, se_lit_248]
  have h2 := exit_spec be sp ra ctx st r15 jb slot st0 (ctx + 304) scell (ctx + 248) h_j h_scell h_s
  rw [h_bl] at h2
  have h3 := longjmp_spec bl jb ((0 : Word) + signExtend12 0x001#12)
    (be + 24 + 4) c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 (sp + signExtend12 0xff0#12)
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 jb (jb + 8) (jb + 16) (jb + 24) (jb + 32) (jb + 40) (jb + 48) (jb + 56) (jb + 64) (jb + 72) (jb + 80) (jb + 88) (jb + 96) (jb + 104)
    (by rw [se_000]; exact BitVec.add_zero _) (by rw [se_lit_8]) (by rw [se_lit_16]) (by rw [se_lit_24]) (by rw [se_lit_32]) (by rw [se_lit_40]) (by rw [se_lit_48]) (by rw [se_lit_56]) (by rw [se_lit_64]) (by rw [se_lit_72]) (by rw [se_lit_80]) (by rw [se_lit_88]) (by rw [se_lit_96]) (by rw [se_lit_104])
  rw [a0_one] at h3
  have e15 : ctx + signExtend12 0x000#12 = ctx := by rw [se_000]; exact BitVec.add_zero _
  rw [e15] at h2
  have h2 := cpsTripleWithin_extend_code hce h2
  have h3 := cpsTripleWithin_extend_code hcl h3
  runBlock h2 h3

end PureInterp.Machine
