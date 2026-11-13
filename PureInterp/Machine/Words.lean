import RiscvZkvm.Rv64.Logic

/-!
# Arrays of doublewords in memory

`words base ws` asserts that the consecutive doublewords starting at `base`
hold `ws`. The operand stack and the instruction table are both arrays of this
kind; `words_append` is what lets a handler proof take out exactly the cells
it touches and put them back.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64

/-- Consecutive doublewords from `base`. -/
def words (base : Word) : List Word → Assertion
  | [] => empAssertion
  | w :: ws => (base ↦ₘ w) ** words (base + 8) ws

@[simp] theorem words_nil (base : Word) : words base [] = empAssertion := rfl

theorem words_cons (base w : Word) (ws : List Word) :
    words base (w :: ws) = ((base ↦ₘ w) ** words (base + 8) ws) := rfl

theorem words_pcFree (base : Word) (ws : List Word) : (words base ws).pcFree := by
  induction ws generalizing base with
  | nil => exact pcFree_emp
  | cons w ws ih => exact pcFree_sepConj (by pcFree) (ih _)

instance (base : Word) (ws : List Word) : Assertion.PCFree (words base ws) :=
  ⟨words_pcFree base ws⟩

instance (base : Word) (bs : List (BitVec 8)) : Assertion.PCFree (bytesRegion base bs) :=
  ⟨bytesRegion_pcFree base bs⟩

/-- Split an array at any point. -/
theorem words_append (base : Word) (xs ys : List Word) :
    words base (xs ++ ys) =
      (words base xs ** words (base + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  induction xs generalizing base with
  | nil => simp [sepConj_emp_left']
  | cons x xs ih =>
    have e : base + 8 + BitVec.ofNat 64 (8 * xs.length) =
        base + BitVec.ofNat 64 (8 * (xs.length + 1)) := by
      rw [Nat.mul_add, BitVec.ofNat_add]; bv_omega
    simp only [List.cons_append, words_cons, ih, List.length_cons, sepConj_assoc', e]

/-- Take out the cell at index `i`. -/
theorem words_at (base : Word) (ws : List Word) (i : Nat) (h : i < ws.length) :
    words base ws =
      (words base (ws.take i) **
        ((base + BitVec.ofNat 64 (8 * i)) ↦ₘ ws[i]) **
        words (base + BitVec.ofNat 64 (8 * (i + 1))) (ws.drop (i + 1))) := by
  have hs : ws = ws.take i ++ ws[i] :: ws.drop (i + 1) := by simp
  conv => lhs; rw [hs]
  rw [words_append, words_cons]
  have hl : (ws.take i).length = i := by simp; omega
  have e : base + BitVec.ofNat 64 (8 * i) + 8 = base + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [Nat.mul_add, BitVec.ofNat_add]; bv_omega
  rw [hl, e]

end PureInterp.Machine
