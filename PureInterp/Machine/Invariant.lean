import PureInterp.Machine.Words
import PureInterp.Model

/-!
# The interpreter invariant

`interp L scr limbs depth gas pc` describes the machine at the entry of an
opcode handler: the pinned registers of the handler calling convention, the
operand stack array, the padded bytecode buffer and the instruction table.
`Rep` ties the stack array to a model state.

Handler theorems are restated as: from `interp … s`, reach the entry of the
next handler with `interp … s'`, where `s'` is what `Model.step` gives.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64

/-- What stays fixed while the interpreter loop runs. -/
structure Layout where
  /-- Machine stack pointer and return address at handler entry. -/
  sp : Word
  ra : Word
  /-- Address of operand stack slot 0. -/
  bottom : Word
  /-- Address of the padded bytecode buffer. -/
  codeBase : Word
  /-- Address of the 256-entry instruction table. -/
  tbl : Word
  /-- Contents of the bytecode buffer. -/
  code : List (BitVec 8)
  /-- Contents of the instruction table: one handler address per opcode. -/
  table : List Word

/-- Caller-saved registers and the one frame slot that handlers use freely. -/
structure Scratch where
  r5 : Word
  r6 : Word
  r16 : Word
  r17 : Word
  r28 : Word
  r29 : Word
  r30 : Word
  r31 : Word
  slot : Word
  /-- `t2`, used by SUB. -/
  r7 : Word

/-- The four little-endian limbs of an EVM word. -/
def limbsOf (w : BitVec 256) : List Word :=
  [w.extractLsb' 0 64, w.extractLsb' 64 64, w.extractLsb' 128 64, w.extractLsb' 192 64]

/-- Address of the frame slot a handler spills `ra` to. -/
def frameSlot (sp : Word) : Word := sp + signExtend12 0xff0#12 + signExtend12 0x008#12

/-- The machine at a handler entry. `limbs` is the whole operand stack array
    (live slots first, then whatever is above the top). -/
def interp (L : Layout) (scr : Scratch) (limbs : List Word) (depth gas pc : Nat) : Assertion :=
  (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ L.ra) ** (.x2 ↦ᵣ L.sp) ** (.x12 ↦ᵣ L.bottom) **
  (.x13 ↦ᵣ (L.bottom + BitVec.ofNat 64 (32 * depth))) **
  (.x14 ↦ᵣ BitVec.ofNat 64 gas) ** (.x15 ↦ᵣ (L.codeBase + BitVec.ofNat 64 pc)) **
  (.x16 ↦ᵣ scr.r16) ** (.x17 ↦ᵣ scr.r17) ** (.x5 ↦ᵣ scr.r5) ** (.x6 ↦ᵣ scr.r6) **
  (.x7 ↦ᵣ scr.r7) **
  (.x28 ↦ᵣ scr.r28) ** (.x29 ↦ᵣ scr.r29) ** (.x30 ↦ᵣ scr.r30) ** (.x31 ↦ᵣ scr.r31) **
  (frameSlot L.sp ↦ₘ scr.slot) **
  words L.bottom limbs ** bytesRegion L.codeBase L.code ** words L.tbl L.table

/-- The stack array holds the model's stack: slot 0 is the bottom, and the
    array has room for 1024 words plus the one slot handlers may scribble on. -/
structure Rep (limbs : List Word) (stack : List Model.Word256) : Prop where
  size : limbs.length = 4 * 1025
  depth : stack.length ≤ 1024
  live : limbs.take (4 * stack.length) = stack.reverse.flatMap limbsOf

/-! ## Address arithmetic -/

/-- Stepping back `k` bytes from the top of a stack of `d` words. -/
theorem top_sub (bottom : Word) (d k : Nat) (hk : k ≤ 32 * d) (hk' : k ≤ 4096) :
    bottom + BitVec.ofNat 64 (32 * d) + BitVec.ofNat 64 (2 ^ 64 - k) =
      bottom + BitVec.ofNat 64 (32 * d - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem se_fc0 : signExtend12 0xfc0#12 = BitVec.ofNat 64 (2 ^ 64 - 64) := by decide
theorem se_fc8 : signExtend12 0xfc8#12 = BitVec.ofNat 64 (2 ^ 64 - 56) := by decide
theorem se_fd0 : signExtend12 0xfd0#12 = BitVec.ofNat 64 (2 ^ 64 - 48) := by decide
theorem se_fd8 : signExtend12 0xfd8#12 = BitVec.ofNat 64 (2 ^ 64 - 40) := by decide
theorem se_fe0 : signExtend12 0xfe0#12 = BitVec.ofNat 64 (2 ^ 64 - 32) := by decide
theorem se_fe8 : signExtend12 0xfe8#12 = BitVec.ofNat 64 (2 ^ 64 - 24) := by decide
theorem se_ff0 : signExtend12 0xff0#12 = BitVec.ofNat 64 (2 ^ 64 - 16) := by decide
theorem se_ff8 : signExtend12 0xff8#12 = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide

/-- A handler's frame is popped exactly: `sp - 16 + 16 = sp`. -/
theorem frame_restore (sp : Word) : sp + signExtend12 0xff0#12 + signExtend12 0x010#12 = sp := by
  have : signExtend12 0xff0#12 + signExtend12 0x010#12 = (0 : Word) := by decide
  rw [BitVec.add_assoc, this]
  exact BitVec.add_zero sp

end PureInterp.Machine
