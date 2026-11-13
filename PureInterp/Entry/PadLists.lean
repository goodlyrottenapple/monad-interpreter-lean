import PureInterp.Entry.Bytes

/-!
# List facts for `Intercode::pad`: the three overwrites give `zeros ++ code ++ zeros`
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

theorem splice_zero (L xs : List (BitVec 8)) : splice L 0 xs = xs ++ L.drop xs.length := by
  simp [splice]

theorem splice_append_left (A R xs : List (BitVec 8)) (i : Nat) (hi : A.length = i) :
    splice (A ++ R) i xs = A ++ xs ++ R.drop xs.length := by
  subst hi
  simp [splice, List.drop_append]

/-- The buffer after `pad`: 30 zero bytes, the code, 33 zero bytes. -/
theorem pad_bytes (L xs : List (BitVec 8)) (n : Nat) (hL : L.length = n + 63)
    (hx : xs.length = n) :
    splice (splice (splice L 0 (List.replicate 30 0)) 30 xs) (30 + n) (List.replicate 33 0)
      = List.replicate 30 0 ++ xs ++ List.replicate 33 0 := by
  rw [splice_zero, splice_append_left _ _ _ 30 (by simp),
    splice_append_left (List.replicate 30 0 ++ xs) _ _ (30 + n) (by rw [List.length_append, List.length_replicate, hx])]
  have : (List.drop (List.replicate 33 (0 : BitVec 8)).length
      (List.drop xs.length (List.drop (List.replicate 30 (0 : BitVec 8)).length L))) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [hL, hx]; omega
  rw [this, List.append_nil]

theorem set_eq_splice_one (bs : List (BitVec 8)) (i : Nat) (b : BitVec 8) (h : i < bs.length) :
    bs.set i b = splice bs i [b] := by
  have := splice_set bs i [] b (by simpa using h)
  simpa using this

theorem take_one_drop (sbs : List (BitVec 8)) (j : Nat) (h : j < sbs.length) :
    (sbs.drop j).take 1 = [sbs.getD j 0] := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

end PureInterp.Entry
