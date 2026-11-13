import PureInterp.Model
import PureInterp.Spec.Step

/-!
# RETURN in the specification

`EVM.X` on RETURN: the memory-expansion charge, the three ways it ends
(success, out of gas, stack underflow), and the output when memory holds only
zeros, which is all the model's opcodes can leave there.
-/

namespace PureInterp.Spec
open EvmYul EVM

/-! ## Reading zero memory -/

/-- `zeroes` takes a `USize`; below `2^32` the length survives on every platform. -/
theorem usize_sub_toNat (a b : ℕ) (hb : b ≤ a) (ha : a < 2 ^ 32) :
    (USize.ofBitVec ((a : BitVec System.Platform.numBits) - (b : BitVec System.Platform.numBits))).toNat = a - b := by
  have hN : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  rw [USize.toNat_ofBitVec, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.natCast_eq_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2 ^ System.Platform.numBits),
    Nat.mod_eq_of_lt (by omega : b < 2 ^ System.Platform.numBits)]
  rw [show 2 ^ System.Platform.numBits - b + a = (a - b) + 2 ^ System.Platform.numBits by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem readWithoutPadding_zero (m : ByteArray) (hz : m.data = Array.replicate m.size 0) (off len : ℕ) :
    ∃ k, k ≤ len ∧ m.readWithoutPadding off len = ⟨Array.replicate k 0⟩ := by
  unfold ByteArray.readWithoutPadding
  split
  · exact ⟨0, by omega, rfl⟩
  · refine ⟨min (off + min len m.size) m.size - off, by omega, ?_⟩
    apply ByteArray.ext
    rw [ByteArray.data_extract, hz]
    apply Array.ext'
    simp

/-- Reading `len < 2^32` bytes from all-zero memory gives `len` zero bytes,
    wherever the read starts and however much memory is materialised. -/
theorem readWithPadding_zero (m : ByteArray) (hz : m.data = Array.replicate m.size 0) (off len : ℕ)
    (hlen : len < 2 ^ 32) :
    m.readWithPadding off len = ⟨Array.replicate len 0⟩ := by
  obtain ⟨k, hk, hread⟩ := readWithoutPadding_zero m hz off len
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  simp only [hread]
  have hs : (⟨Array.replicate k 0⟩ : ByteArray).size = k := by simp [ByteArray.size]
  apply ByteArray.ext
  rw [ByteArray.data_append, hs]
  show Array.replicate k 0 ++ Array.replicate _ 0 = _
  rw [usize_sub_toNat len k hk hlen]
  apply Array.ext'
  simp
  omega

theorem toByteArray_zeros (n : ℕ) :
    Model.toByteArray (List.replicate n 0) = ⟨Array.replicate n 0⟩ := by
  apply ByteArray.ext
  apply Array.ext'
  simp [Model.toByteArray]

/-! ## The memory-expansion charge -/

theorem Cm_eq (a : UInt256) : Cₘ a = Model.cmem a.toNat := by
  simp [Cₘ, Model.cmem, GasConstants.Gmemory, Cₘ.QuadraticCeofficient]

theorem M_eq (s f l : ℕ) :
    MachineState.M s f l = if l = 0 then s else max s ((f + l + 31) / 32) := by
  cases l <;> simp [MachineState.M]

theorem toNat_ofNat_lt (n : ℕ) (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := by
  show (Fin.ofNat _ n).val = n
  simp only [Fin.ofNat]
  exact Nat.mod_eq_of_lt (by rw [Refine.size_eq]; exact h)

theorem cmem_mono {a b : ℕ} (h : a ≤ b) : Model.cmem a ≤ Model.cmem b := by
  unfold Model.cmem
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 h) (Nat.div_le_div_right (Nat.mul_le_mul h h))

/-- The charge `X` makes for RETURN with `off` and `size` on top of the stack. -/
theorem memCost_return (s : EVM.State) (off size : UInt256) (rest : List UInt256)
    (hst : s.stack = off :: size :: rest) :
    memoryExpansionCost s .RETURN =
      Model.cmem (if size.toNat = 0 then s.activeWords.toNat
        else max s.activeWords.toNat ((off.toNat + size.toNat + 31) / 32)) -
      Model.cmem s.activeWords.toNat := by
  have ho' : off.toNat < 2 ^ 256 := Nat.lt_of_lt_of_eq off.val.isLt Refine.size_eq
  have hz' : size.toNat < 2 ^ 256 := Nat.lt_of_lt_of_eq size.val.isLt Refine.size_eq
  have ha' : s.activeWords.toNat < 2 ^ 256 := Nat.lt_of_lt_of_eq s.activeWords.val.isLt Refine.size_eq
  have e : memoryExpansionCost s .RETURN =
      Cₘ (.ofNat (MachineState.M s.activeWords.toNat off.toNat size.toNat)) - Cₘ s.activeWords := by
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hst]
  rw [e, Cm_eq, Cm_eq, M_eq, toNat_ofNat_lt]
  split <;> omega

/-! ## `X` on RETURN -/

theorem step_return (f c : ℕ) (st : EVM.State) :
    EVM.step (f + 1) c (some (.RETURN, none)) st =
      EVM.binaryMachineStateOp MachineState.evmReturn
        { st with execLength := st.execLength + 1,
                  gasAvailable := st.gasAvailable - UInt256.ofNat c } := by
  rfl

theorem cost_return (t : EVM.State) : C' t .RETURN = 0 := by
  simp [C', GasConstants.Gzero, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero]

/-- RETURN with the expansion charge covered: success, with the charged gas
    and the returned memory range as output. -/
theorem X_return (f : ℕ) (vj : Array UInt256) (s : EVM.State) (off size : UInt256)
    (rest : List UInt256)
    (hdec : decode s.executionEnv.code s.pc = some (.RETURN, none))
    (hst : s.stack = off :: size :: rest)
    (hgas : memoryExpansionCost s .RETURN ≤ s.gasAvailable.toNat)
    (hlen : rest.length + 2 ≤ 1024) :
    ∃ e, X (f + 2) vj s = .ok (.success e (s.memory.readWithPadding off.toNat size.toNat)) ∧
      e.gasAvailable = s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .RETURN) := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hg : ¬ s.gasAvailable.toNat < memoryExpansionCost s .RETURN := by omega
  have hl : ¬ (1024 < rest.length) := by omega
  have hu : ¬ (rest.length + 1 + 1 < 2) := by omega
  simp [cost_return, δ, α, hst, sub_ofNat_zero, hg, hl, hu, Operation.isCreate, step_return,
    binaryMachineStateOp, Stack.pop2, MachineState.evmReturn]
  dsimp only [pure, Except.pure]
  exact ⟨_, rfl, sub_ofNat_zero _⟩

/-- RETURN without the gas for its memory expansion. -/
theorem X_return_oog (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (.RETURN, none))
    (hgas : s.gasAvailable.toNat < memoryExpansionCost s .RETURN) :
    X (f + 1) vj s = .error .OutOfGass := by
  rw [X]
  simp only [hdec, Option.getD_some]
  simp [hgas]
  rfl

/-- RETURN with fewer than two operands: an exceptional halt. -/
theorem X_return_underflow (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (.RETURN, none))
    (hlen : s.stack.length < 2) :
    ∃ err, X (f + 1) vj s = .error err ∧ err ≠ .OutOfFuel := by
  by_cases hg : s.gasAvailable.toNat < memoryExpansionCost s .RETURN
  · exact ⟨_, X_return_oog f vj s hdec hg, fun h => by cases h⟩
  · refine ⟨.StackUnderflow, ?_, fun h => by cases h⟩
    rw [X]
    simp only [hdec, Option.getD_some]
    simp [cost_return, δ, hg, hlen]
    rfl

end PureInterp.Spec
