import PureInterp.Entry.Setjmp
import PureInterp.Entry.CoreLoop
import PureInterp.Entry.Trampoline
import PureInterp.Entry.Bytes

/-!
# From the call of `trampoline` to the first handler, and back out

`launch_spec` chains `trampoline` (entry) → `setjmp` (returns 0) →
`trampoline` (stores the jump buffer in the context, calls `core_loop`) →
`core_loop` → entry of the handler `h` of the first opcode byte.

At that point the machine is in the shape of `Machine.interp … 0 gas 0 **
Machine.exitFrame …` with
`L.sp = spf = sp - 256`, `L.ra = bt + 72`, `L.bottom = stk`, `E.ctx = ctx`,
`E.jb = jb = spf + 32`, `E.v0 = bt + 32` (the `setjmp` return site),
`E.v1 … E.v12 = E.c0 … E.c11` (the callee-saved registers `c0 … c11`) and
`E.v13 = spf`. The statements here are in raw atoms.

`trampoline_leave` (in `Trampoline.lean`) is the way back: from the `setjmp`
return site `bt + 32` with `a0 ≠ 0` to the caller of `trampoline`;
`trampoline_exit` restates it with the caller's `sp`.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-- `trampoline(ctx, ic, stk, fn = core_loop)` up to the first handler. The
    first opcode byte is read from the doubleword `cwAddr ↦ₘ cw` containing
    the instruction pointer `ip` (the content of the intercode's first field). -/
theorem launch_spec (cr : CodeReq) (bt bs bc sp ra ctx ic stk fn r14 r15 r16 : Word)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Word) (s0 s1 s2 s3 s4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Word)
    (spf jb jb0 gas ip cw cwAddr h : Word)
    (cslot rslot fslot islot sslot j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 jcell gcell acell tcell : Word)
    (hct : ∀ a i, CodeReq.ofProg bt Image.f_trampoline.prog a = some i → cr a = some i)
    (hcs : ∀ a i, CodeReq.ofProg bs Image.f_setjmp.prog a = some i → cr a = some i)
    (hcc : ∀ a i, CodeReq.ofProg bc Image.f_core_loop.prog a = some i → cr a = some i)
    (h_spf : sp + signExtend12 0xf00#12 = spf)
    (h_jb : spf + signExtend12 0x020#12 = jb)
    (h_bs : bt + 28 + signExtend21 0x00128c#21 = bs)
    (h_ret : (bt + 28 + 4 + signExtend12 0x000#12) &&& ~~~1 = bt + 32)
    (h_fn : (fn + signExtend12 0x000#12) &&& ~~~1 = bc)
    (h_cslot : spf + signExtend12 0x000#12 = cslot)
    (h_rslot : spf + signExtend12 0x0f8#12 = rslot)
    (h_fslot : spf + signExtend12 0x008#12 = fslot)
    (h_islot : spf + signExtend12 0x010#12 = islot)
    (h_sslot : spf + signExtend12 0x018#12 = sslot)
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
    (h_jcell : ctx + signExtend12 0x130#12 = jcell)
    (h_gcell : ctx + signExtend12 0x008#12 = gcell)
    (h_acell : ic + signExtend12 0x000#12 = acell)
    (halign : alignToDword ip = cwAddr)
    (hvalid : isValidByteAccess ip = true)
    (h_tcell : bc + (8 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0x140#12 +
        (((extractByte cw (byteOffset ip)).zeroExtend 64) <<< (0x03#6).toNat) = tcell) :
    cpsTripleWithin 46 bt ((h + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ c0) ** (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) ** (.x19 ↦ᵣ c3) ** (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) ** (.x22 ↦ᵣ c6) ** (.x23 ↦ᵣ c7) ** (.x24 ↦ᵣ c8) ** (.x25 ↦ᵣ c9) ** (.x26 ↦ᵣ c10) ** (.x27 ↦ᵣ c11) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) ** (.x13 ↦ᵣ fn) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) ** (.x16 ↦ᵣ r16) **
       (cslot ↦ₘ s0) ** (rslot ↦ₘ s1) ** (fslot ↦ₘ s2) ** (islot ↦ₘ s3) ** (sslot ↦ₘ s4) **
       (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) ** (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) ** (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13) **
       (jcell ↦ₘ jb0) ** (gcell ↦ₘ gas) ** (acell ↦ₘ ip) ** (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bt + 68 + 4)) ** (.x2 ↦ᵣ spf) **
       (.x8 ↦ᵣ c0) ** (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) ** (.x19 ↦ᵣ c3) ** (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) ** (.x22 ↦ᵣ c6) ** (.x23 ↦ᵣ c7) ** (.x24 ↦ᵣ c8) ** (.x25 ↦ᵣ c9) ** (.x26 ↦ᵣ c10) ** (.x27 ↦ᵣ c11) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) ** (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ gas) **
       (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ h) **
       (cslot ↦ₘ ctx) ** (rslot ↦ₘ ra) ** (fslot ↦ₘ fn) ** (islot ↦ₘ ic) ** (sslot ↦ₘ stk) **
       (j0 ↦ₘ (bt + 28 + 4)) ** (j1 ↦ₘ c0) ** (j2 ↦ₘ c1) ** (j3 ↦ₘ c2) ** (j4 ↦ₘ c3) ** (j5 ↦ₘ c4) ** (j6 ↦ₘ c5) ** (j7 ↦ₘ c6) ** (j8 ↦ₘ c7) ** (j9 ↦ₘ c8) ** (j10 ↦ₘ c9) ** (j11 ↦ₘ c10) ** (j12 ↦ₘ c11) ** (j13 ↦ₘ spf) **
       (jcell ↦ₘ jb) ** (gcell ↦ₘ gas) **
       (acell ↦ₘ ip) ** (cwAddr ↦ₘ cw) ** (tcell ↦ₘ h)) := by
  subst h_spf
  have h1 := trampoline_enter bt sp ra ctx ic stk fn s0 s1 s2 s3 s4 cslot rslot fslot islot sslot
    h_cslot h_rslot h_fslot h_islot h_sslot
  rw [h_bs, h_jb] at h1
  generalize sp + signExtend12 0xf00#12 = spf at *
  have h2 := setjmp_spec bs jb (bt + 28 + 4)
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 spf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13
    h_j0 h_j1 h_j2 h_j3 h_j4 h_j5 h_j6 h_j7 h_j8 h_j9 h_j10 h_j11 h_j12 h_j13
  rw [h_ret] at h2
  simp only [add_se12_zero] at h2
  have h3 := trampoline_call bt spf (bt + 28 + 4)
    ((0 : Word) + signExtend12 0x000#12) ic stk fn r14 r15 ctx ic stk fn jb0
    cslot fslot islot sslot jcell (by decide) h_cslot h_fslot h_islot h_sslot h_jcell
  rw [h_fn, h_jb] at h3
  simp only [add_se12_zero] at h3
  have h4 := core_loop_spec bc 0 ctx ic stk 0 fn r16 ip cw cwAddr gas h acell gcell tcell
    h_acell (by rw [add_se12_zero]; exact h_gcell) (by rw [add_se12_zero]; exact halign)
    (by rw [add_se12_zero]; exact hvalid) (by rw [add_se12_zero, add_se12_zero]; exact h_tcell)
  simp only [add_se12_zero] at h4
  rw [add_se12_zero]
  have h1 := cpsTripleWithin_extend_code hct h1
  have h2 := cpsTripleWithin_extend_code hcs h2
  have h3 := cpsTripleWithin_extend_code hct h3
  have h4 := cpsTripleWithin_extend_code hcc h4
  runBlock h1 h2 h3 h4

/-- `launch_spec` with the bytecode as a region: `ip = cbase + i` points into
    an aligned `bytesRegion cbase cbytes`, and `h` is the table entry of the
    byte `cbytes[i]`. -/
theorem launch_region (cr : CodeReq) (bt bs bc sp ra ctx ic stk fn r14 r15 r16 : Word)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Word) (s0 s1 s2 s3 s4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Word)
    (spf jb jb0 gas ip cbase h : Word)
    (cslot rslot fslot islot sslot j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 jcell gcell acell tcell : Word)
    (cbytes : List (BitVec 8)) (i : Nat)
    (hct : ∀ a i, CodeReq.ofProg bt Image.f_trampoline.prog a = some i → cr a = some i)
    (hcs : ∀ a i, CodeReq.ofProg bs Image.f_setjmp.prog a = some i → cr a = some i)
    (hcc : ∀ a i, CodeReq.ofProg bc Image.f_core_loop.prog a = some i → cr a = some i)
    (h_spf : sp + signExtend12 0xf00#12 = spf)
    (h_jb : spf + signExtend12 0x020#12 = jb)
    (h_bs : bt + 28 + signExtend21 0x00128c#21 = bs)
    (h_ret : (bt + 28 + 4 + signExtend12 0x000#12) &&& ~~~1 = bt + 32)
    (h_fn : (fn + signExtend12 0x000#12) &&& ~~~1 = bc)
    (h_cslot : spf + signExtend12 0x000#12 = cslot)
    (h_rslot : spf + signExtend12 0x0f8#12 = rslot)
    (h_fslot : spf + signExtend12 0x008#12 = fslot)
    (h_islot : spf + signExtend12 0x010#12 = islot)
    (h_sslot : spf + signExtend12 0x018#12 = sslot)
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
    (h_jcell : ctx + signExtend12 0x130#12 = jcell)
    (h_gcell : ctx + signExtend12 0x008#12 = gcell)
    (h_acell : ic + signExtend12 0x000#12 = acell)
    (h_ip : ip = cbase + BitVec.ofNat 64 i)
    (calign : cbase.toNat % 8 = 0) (hi : i < cbytes.length)
    (cover : cbase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (cbase + BitVec.ofNat 64 i) = true)
    (h_tcell : bc + (8 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 +
        signExtend12 0x140#12 +
        (((cbytes[i]'hi).zeroExtend 64) <<< (0x03#6).toNat) = tcell) :
    cpsTripleWithin 46 bt ((h + signExtend12 0x000#12) &&& ~~~1) cr
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x8 ↦ᵣ c0) ** (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) ** (.x19 ↦ᵣ c3) ** (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) ** (.x22 ↦ᵣ c6) ** (.x23 ↦ᵣ c7) ** (.x24 ↦ᵣ c8) ** (.x25 ↦ᵣ c9) ** (.x26 ↦ᵣ c10) ** (.x27 ↦ᵣ c11) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) ** (.x13 ↦ᵣ fn) ** (.x14 ↦ᵣ r14) **
       (.x15 ↦ᵣ r15) ** (.x16 ↦ᵣ r16) **
       (cslot ↦ₘ s0) ** (rslot ↦ₘ s1) ** (fslot ↦ₘ s2) ** (islot ↦ₘ s3) ** (sslot ↦ₘ s4) **
       (j0 ↦ₘ v0) ** (j1 ↦ₘ v1) ** (j2 ↦ₘ v2) ** (j3 ↦ₘ v3) ** (j4 ↦ₘ v4) ** (j5 ↦ₘ v5) ** (j6 ↦ₘ v6) ** (j7 ↦ₘ v7) ** (j8 ↦ₘ v8) ** (j9 ↦ₘ v9) ** (j10 ↦ₘ v10) ** (j11 ↦ₘ v11) ** (j12 ↦ₘ v12) ** (j13 ↦ₘ v13) **
       (jcell ↦ₘ jb0) ** (gcell ↦ₘ gas) ** (acell ↦ₘ ip) ** bytesRegion cbase cbytes ** (tcell ↦ₘ h))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (bt + 68 + 4)) ** (.x2 ↦ᵣ spf) **
       (.x8 ↦ᵣ c0) ** (.x9 ↦ᵣ c1) ** (.x18 ↦ᵣ c2) ** (.x19 ↦ᵣ c3) ** (.x20 ↦ᵣ c4) ** (.x21 ↦ᵣ c5) ** (.x22 ↦ᵣ c6) ** (.x23 ↦ᵣ c7) ** (.x24 ↦ᵣ c8) ** (.x25 ↦ᵣ c9) ** (.x26 ↦ᵣ c10) ** (.x27 ↦ᵣ c11) **
       (.x10 ↦ᵣ ctx) ** (.x11 ↦ᵣ ic) ** (.x12 ↦ᵣ stk) ** (.x13 ↦ᵣ stk) ** (.x14 ↦ᵣ gas) **
       (.x15 ↦ᵣ ip) ** (.x16 ↦ᵣ h) **
       (cslot ↦ₘ ctx) ** (rslot ↦ₘ ra) ** (fslot ↦ₘ fn) ** (islot ↦ₘ ic) ** (sslot ↦ₘ stk) **
       (j0 ↦ₘ (bt + 28 + 4)) ** (j1 ↦ₘ c0) ** (j2 ↦ₘ c1) ** (j3 ↦ₘ c2) ** (j4 ↦ₘ c3) ** (j5 ↦ₘ c4) ** (j6 ↦ₘ c5) ** (j7 ↦ₘ c6) ** (j8 ↦ₘ c7) ** (j9 ↦ₘ c8) ** (j10 ↦ₘ c9) ** (j11 ↦ₘ c10) ** (j12 ↦ₘ c11) ** (j13 ↦ₘ spf) **
       (jcell ↦ₘ jb) ** (gcell ↦ₘ gas) **
       (acell ↦ₘ ip) ** bytesRegion cbase cbytes ** (tcell ↦ₘ h)) := by
  subst h_ip
  have hq : 8 * (i / 8) < cbytes.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at cbase cbytes (i / 8) hq
  have hbyte : extractByte (packBytes ((cbytes.drop (8 * (i / 8))).take 8))
      (byteOffset (cbase + BitVec.ofNat 64 i)) = cbytes[i]'hi := by
    rw [byteOffset_add_ofNat_of_aligned calign cover,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  have T := launch_spec cr bt bs bc sp ra ctx ic stk fn r14 r15 r16 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 s0 s1 s2 s3 s4 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
    spf jb jb0 gas (cbase + BitVec.ofNat 64 i) (packBytes ((cbytes.drop (8 * (i / 8))).take 8))
    (cbase + BitVec.ofNat 64 (8 * (i / 8))) h
    cslot rslot fslot islot sslot j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 jcell gcell acell tcell
    hct hcs hcc h_spf h_jb h_bs h_ret h_fn h_cslot h_rslot h_fslot h_islot h_sslot
    h_j0 h_j1 h_j2 h_j3 h_j4 h_j5 h_j6 h_j7 h_j8 h_j9 h_j10 h_j11 h_j12 h_j13 h_jcell h_gcell h_acell
    (alignToDword_add_ofNat_of_aligned calign cover) hvalid (by rw [hbyte]; exact h_tcell)
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) T)

/-- The trampoline's frame is popped exactly: `sp - 256 + 256 = sp`. -/
theorem tramp_frame (sp spf : Word) (h : sp + signExtend12 0xf00#12 = spf) :
    spf + signExtend12 0x100#12 = sp := by
  subst h
  rw [BitVec.add_assoc, show signExtend12 0xf00#12 + signExtend12 0x100#12 = (0 : Word) from by decide]
  exact BitVec.add_zero sp

/-- From the `setjmp` return site with `a0 ≠ 0` (after `longjmp`) back to the
    caller of `trampoline`, whose `sp` is restored (`spf = sp - 256` is the
    trampoline's frame pointer). -/
theorem trampoline_exit (bt sp spf r1 a0 ra rslot : Word) (ha0 : a0 ≠ 0)
    (h_spf : sp + signExtend12 0xf00#12 = spf)
    (h_rslot : spf + signExtend12 0x0f8#12 = rslot) :
    cpsTripleWithin 4 (bt + 32) ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg bt Image.f_trampoline.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ r1) ** (.x2 ↦ᵣ spf) ** (.x10 ↦ᵣ a0) ** (rslot ↦ₘ ra))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ a0) ** (rslot ↦ₘ ra)) := by
  have h := trampoline_leave bt spf r1 a0 ra rslot ha0 h_rslot
  rw [tramp_frame sp spf h_spf] at h
  exact h

end PureInterp.Entry
