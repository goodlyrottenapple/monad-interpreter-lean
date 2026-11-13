import PureInterp.Image.Link

/-!
# The instruction table and pc-relative link equations

`imageTable` is the interpreter's 256-entry dispatch table
(`monad::vm::interpreter::instruction_table<EvmTraits<Cancun>>`, at
`0xa0000150` in the read-only data segment), read out of `Image.data0.bytes`.
What each entry is, is in the generated `LinkTableEntries.lean`.

## Recipe for pc-relative equations

An equation between concrete addresses, such as

    Image.f_add.addr + 180 + signExtend21 0x007de4#21 = Image.f_rt_Context_exit.addr

is a closed bit-vector equation; `by decide` proves it (the `.addr`
definitions unfold during evaluation), in a few milliseconds. `link_eq` is
that, as a named tactic. Three worked examples are at the end of this file.
To discharge a hypothesis stated over variables (`hA + 180 + … = E.be`),
instantiate the variables with the `Image.f_x.addr` constants and `tableAddr`
and close the resulting goal with `link_eq`.
-/

set_option maxRecDepth 100000

open RiscvZkvm.Rv64

namespace PureInterp.Image

/-- Address of `instruction_table` (see `build/pure.map`). -/
def tableAddr : Word := 0xa0000150

/-- Index of the table's first doubleword in the data segment. -/
def tableDword : Nat := 42

/-- The dispatch table: 256 little-endian doublewords of the data segment. -/
def imageTable : List Word := (List.range 256).map fun n => dataWord (tableDword + n)

theorem imageTable_length : imageTable.length = 256 := by simp [imageTable]

theorem imageTable_getD {n : Nat} (h : n < 256) :
    imageTable.getD n 0 = dataWord (tableDword + n) := by
  simp [imageTable, List.getD, h]

theorem tableAddr_eq : tableAddr = data0.addr + BitVec.ofNat 64 (8 * tableDword) := by decide

/-- In a loaded state, the memory doubleword at table slot `n` is
`imageTable`'s entry `n`. -/
theorem ImageLoaded.table {s : MachineState} (h : ImageLoaded s) {n : Nat} (hn : n < 256) :
    s.mem (tableAddr + BitVec.ofNat 64 (8 * n)) = imageTable.getD n 0 := by
  have hlen : data0.bytes.length = 2408 := by decide
  have hd := h.data (tableDword + n) (by rw [hlen]; simp only [tableDword]; omega)
  rw [imageTable_getD hn, ← hd, tableAddr_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Closes a closed equation between concrete addresses. -/
macro "link_eq" : tactic => `(tactic| decide)

/-! ### Worked examples -/

/-- `auipc`/`addi` pair in ADD computing the table address. -/
example :
    f_add.addr + (136 : Word)
        + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
        + signExtend12 0x24c#12 = tableAddr := by link_eq

theorem add_table_ref :
    f_add.addr + (136 : Word)
        + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
        + signExtend12 0x24c#12 = tableAddr := by link_eq

/-- ADD's out-of-gas `jal` to `Context::exit`. -/
theorem add_oog_exit_ref :
    f_add.addr + 180 + signExtend21 0x007de4#21 = f_rt_Context_exit.addr := by link_eq

/-- `Context::exit`'s `jal` to `longjmp`. -/
theorem exit_longjmp_ref :
    f_rt_Context_exit.addr + 24 + signExtend21 0x000044#21 = f_longjmp.addr := by link_eq

end PureInterp.Image
