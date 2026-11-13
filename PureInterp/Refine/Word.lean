import EvmYul.EVM.Semantics
import PureInterp.U256

/-!
# Relating machine values to specification values

The interpreter keeps an EVM word as four 64-bit limbs and the gas counter as
a signed 64-bit integer; EVMYulLean uses `UInt256` (a `Fin 2^256`) for both.
-/

namespace PureInterp.Refine
open EvmYul RiscvZkvm.Rv64

theorem size_eq : UInt256.size = 2 ^ 256 := by
  simp [UInt256.size]

/-- The specification word with the same value as a 256-bit vector. -/
def u256 (x : BitVec 256) : UInt256 := ⟨⟨x.toNat, by rw [size_eq]; exact x.isLt⟩⟩

@[simp] theorem u256_toNat (x : BitVec 256) : (u256 x).toNat = x.toNat := rfl

theorem u256_injective {x y : BitVec 256} (h : u256 x = u256 y) : x = y := by
  have := congrArg UInt256.toNat h
  simp at this
  exact BitVec.eq_of_toNat_eq this

/-- Machine addition of 256-bit vectors is the specification's ADD. -/
theorem u256_add (x y : BitVec 256) : u256 (x + y) = u256 x + u256 y := by
  apply congrArg UInt256.mk
  apply Fin.ext
  show (x + y).toNat = ((u256 x).val + (u256 y).val).val
  rw [Fin.val_add]
  simp [u256, BitVec.toNat_add, size_eq]

/-- Machine subtraction of 256-bit vectors is the specification's SUB. -/
theorem u256_sub (x y : BitVec 256) : u256 (x - y) = u256 x - u256 y := by
  apply congrArg UInt256.mk
  apply Fin.ext
  show (x - y).toNat = ((u256 x).val - (u256 y).val).val
  rw [Fin.sub_def]
  simp only [u256, BitVec.toNat_sub, size_eq]

/-- The gas charge `addi a4, a4, -c` on a counter that holds `g`. -/
theorem gas_charge (g : Word) (c : Nat) (imm : BitVec 12) (hc : c < 2048)
    (himm : imm = BitVec.ofNat 12 (4096 - c)) (hg : g.toNat < 2 ^ 63) (hpos : 0 < c) :
    (¬ BitVec.slt (g + signExtend12 imm) 0 ↔ c ≤ g.toNat) ∧
    (c ≤ g.toNat → (g + signExtend12 imm).toNat = g.toNat - c) := by
  subst himm
  have hse : signExtend12 (BitVec.ofNat 12 (4096 - c)) = BitVec.ofNat 64 (2 ^ 64 - c) := by
    unfold signExtend12
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
    split <;> omega
  rw [hse]
  constructor
  · rw [BitVec.slt_iff_toInt_lt]
    simp [BitVec.toInt_eq_toNat_cond, BitVec.toNat_add]
    constructor <;> intro h <;> (try split at h) <;> omega
  · intro h
    simp [BitVec.toNat_add]
    omega

end PureInterp.Refine
