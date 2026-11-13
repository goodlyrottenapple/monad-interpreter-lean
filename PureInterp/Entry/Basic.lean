import RiscvZkvm.Rv64.Logic
import PureInterp.Image.Index

/-!
# Small helpers shared by the entry/exit glue proofs
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

/-- The pure fact at the end of a branch postcondition. -/
theorem pure_end2 {A B : Assertion} {P : Prop} : ∀ h, (A ** B ** ⌜P⌝) h → P := by
  intro h hp
  rw [← sepConj_assoc] at hp
  exact ((sepConj_pure_right h).1 hp).2

/-- A triple whose precondition carries a pure fact may assume it. -/
theorem triple_pure_pre {n : Nat} {e x : Word} {cr : CodeReq} {P P' Q : Assertion} {fact : Prop}
    (hperm : ∀ h, P' h → (P ** ⌜fact⌝) h)
    (h : fact → cpsTripleWithin n e x cr P Q) :
    cpsTripleWithin n e x cr P' Q := by
  apply cpsTripleWithin_weaken hperm (fun _ hq => hq)
  by_cases hf : fact
  · exact cpsTripleWithin_strip_pure_and_convert Q (h hf) (fun _ _ hq => hq)
  · intro R hR s hcr ⟨_, _, h1, _, _, _, hPF, _⟩ _
    exact absurd ((sepConj_pure_right h1).1 hPF).2 hf

/-- Zero steps. -/
theorem triple_refl {a : Word} (cr : CodeReq) {P Q : Assertion} (h : ∀ hp, P hp → Q hp) :
    cpsTripleWithin 0 a a cr P Q :=
  cpsTripleWithin_extend_code (fun _ _ hc => by simp [CodeReq.empty] at hc)
    (cpsTripleWithin_refl h)

theorem se12_zero : signExtend12 (0x000#12) = (0 : Word) := by decide
theorem add_se12_zero (b : Word) : b + signExtend12 (0x000#12) = b := by
  rw [se12_zero]; exact BitVec.add_zero b

end PureInterp.Entry
