import PureInterp.Top.Linked
import PureInterp.Spec.Agree

/-!
# The loop theorem for the real image, with EVMYulLean

`loop_correct` puts `Machine.run_sim`, `Top.linked_image` and `Spec.agrees`
together: for a halting run of the model that executes only supported
opcodes, the image's handler loop reaches the `setjmp` return site with the
model's result in the context, and EVMYulLean's `EVM.X` gives that result too.

There is one run restriction, `Spec.RunSupported`: every opcode byte the run
executes is STOP (0x00), ADD (0x01), SUB (0x03), POP (0x50), PUSH1 (0x60),
RETURN (0xf3), or one of the 108 bytes EVMYulLean decodes to `INVALID` (0xfe
and the bytes that are no Cancun instruction). `runOK_of_runSupported` shows
it implies the machine side's `Machine.RunOK` for the image's table: each of
those 108 bytes dispatches to the binary's `invalid` handler. (The converse
fails: the binary also sends 34 real instructions it disables, such as
BALANCE or SLOAD, to `invalid`; on those the model fails and EVMYulLean does
not.)

`loop_correct_machine` restates the result on machine states, with no triple.
-/

namespace PureInterp.Top
open RiscvZkvm.Rv64 PureInterp.Machine

set_option maxRecDepth 100000

/-- Every byte EVMYulLean decodes to `INVALID` dispatches to the binary's
    `invalid` handler. -/
theorem invalid_of_parseInstr : ∀ n, n < 256 →
    EvmYul.EVM.parseInstr (UInt8.ofNat n) = some .INVALID → n ∈ Image.invalidOpcodes := by
  decide

theorem opOK_of_supported {L : Layout} (ht : L.table = Image.imageTable) (b : Model.Byte)
    (h : Spec.Supported b) : OpOK L Image.f_invalid.addr b := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    rw [ht]
    exact (Image.imageTable_invalid_iff _).mpr (invalid_of_parseInstr _ b.isLt h)

/-- The specification side's run restriction implies the machine side's. -/
theorem runOK_of_runSupported {L : Layout} (ht : L.table = Image.imageTable)
    (code : List Model.Byte) :
    ∀ fuel s, Spec.RunSupported code fuel s → RunOK L Image.f_invalid.addr code fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s _; trivial
  | succ n ih =>
    intro s h
    obtain ⟨hb, hrest⟩ := h
    refine ⟨opOK_of_supported ht _ hb, ?_⟩
    cases hstep : Model.step code s with
    | halt r => trivial
    | next s' =>
      rw [hstep] at hrest
      exact ih s' hrest

variable {L : Layout} {E : ExitEnv} {code : List Model.Byte}

/-- **The image's handler loop and EVMYulLean agree.** Let the model halt
    with `r` within `fuel` instructions from `s`, executing only supported
    opcodes. Then, under the run-time layout facts `Dyn`:

    1. from the invariant for `s` at the handler of the current opcode, the
       image reaches the `setjmp` return site within `464 * fuel` instructions
       with the context holding `r` (`ResultOK`); and
    2. from every EVMYulLean state matching `s`, `EVM.X` returns `r`. -/
theorem loop_correct (D : Dyn L E code)
    (fuel : Nat) (s : Model.State) (r : Model.Result)
    (hrun : Model.run code fuel s = some r) (hsup : Spec.RunSupported code fuel s)
    (scr : Scratch) (limbs : List Word) (a1v g0 s2 st0 : Word) (res fr : List Word)
    (hrep : Rep limbs s.stack) (hgas : s.gas < 2 ^ 63) (hpc : s.pc ≤ code.length + 1)
    (hres : res.length = 8) (hfr : fr.length = 10) :
    (∃ scr' limbs' j12 j13 j14 js2 status g res' fr',
      ResultOK r s.mem status g res res' ∧
      cpsTripleWithin (464 * fuel) (Image.imageTable.getD (Model.byteAt code s.pc).toNat 0)
        ((E.v0 + signExtend12 0x000#12) &&& ~~~1) Image.imageCode
        (interp L scr limbs s.stack.length s.gas (30 + s.pc) ** exitFrame E a1v g0 s2 st0 res fr)
        (final L E scr' limbs' j12 j13 j14 js2 status g res' fr')) ∧
    (∀ (vj : Array EvmYul.UInt256) (e : EvmYul.EVM.State), Spec.Matches' code s e →
      Model.ResultMatches r (EvmYul.EVM.X (fuel + 1) vj e)) := by
  refine ⟨?_, fun vj e hm => Spec.agrees code vj fuel s r e hm hsup hrun⟩
  have h := run_sim (linked_image D) fuel s r hrun
    (runOK_of_runSupported D.table code fuel s hsup) scr limbs a1v g0 s2 st0 res fr
    hrep hgas hpc hres hfr
  rw [D.table] at h
  exact h

/-- **`loop_correct` on machine states.** Let `m` be a machine state holding
    the image, with the pc at the image's handler for the current opcode and
    the invariant for `s` (`interp ** exitFrame`) holding of it. Then within
    `464 * fuel` steps of the RV64 model the machine is at the `setjmp` return
    site (the jump buffer's `ra`, bit 0 cleared), the context's status field
    (`ctx + 248`) and gas field (`ctx + 8`) hold a status and gas that
    `ResultOK` ties to the model's result `r`, and `r` is what `EVM.X`
    returns from every matching EVMYulLean state. -/
theorem loop_correct_machine (D : Dyn L E code)
    (fuel : Nat) (s : Model.State) (r : Model.Result)
    (hrun : Model.run code fuel s = some r) (hsup : Spec.RunSupported code fuel s)
    (scr : Scratch) (limbs : List Word) (a1v g0 s2 st0 : Word) (res fr : List Word)
    (hrep : Rep limbs s.stack) (hgas : s.gas < 2 ^ 63) (hpc : s.pc ≤ code.length + 1)
    (hres : res.length = 8) (hfr : fr.length = 10)
    (m : MachineState) (hload : Image.ImageLoaded m)
    (hmpc : m.pc = Image.imageTable.getD (Model.byteAt code s.pc).toNat 0)
    (hpre : (interp L scr limbs s.stack.length s.gas (30 + s.pc) **
      exitFrame E a1v g0 s2 st0 res fr).holdsFor m) :
    ∃ k, k ≤ 464 * fuel ∧ ∃ m', stepN k m = some m' ∧
      m'.pc = (E.v0 + signExtend12 0x000#12) &&& ~~~1 ∧
      ∃ scr' limbs' j12 j13 j14 js2 status g res' fr',
        ResultOK r s.mem status g res res' ∧
        (final L E scr' limbs' j12 j13 j14 js2 status g res' fr').holdsFor m' ∧
        m'.getMem (E.ctx + 248) = status ∧ m'.getMem (E.ctx + 8) = g ∧
        ∀ (vj : Array EvmYul.UInt256) (e : EvmYul.EVM.State), Spec.Matches' code s e →
          Model.ResultMatches r (EvmYul.EVM.X (fuel + 1) vj e) := by
  obtain ⟨⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hok, T⟩, hspec⟩ :=
    loop_correct D fuel s r hrun hsup scr limbs a1v g0 s2 st0 res fr hrep hgas hpc hres hfr
  obtain ⟨k, hk, m', hstep, hpc', hpost⟩ :=
    T empAssertion (by pcFree) m hload.satisfied (by rw [sepConj_emp_right']; exact hpre) hmpc
  rw [sepConj_emp_right'] at hpost
  refine ⟨k, hk, m', hstep, hpc', scr', limbs', j12, j13, j14, js2, status, g, res', fr', hok,
    hpost, ?_, ?_, hspec⟩
  · have h := hpost
    unfold final at h
    iterate 37 replace h := holdsFor_sepConj_elim_right h
    exact holdsFor_memIs_getMem (holdsFor_sepConj_elim_left h)
  · have h := hpost
    unfold final at h
    iterate 34 replace h := holdsFor_sepConj_elim_right h
    exact holdsFor_memIs_getMem (holdsFor_sepConj_elim_left h)

end PureInterp.Top
