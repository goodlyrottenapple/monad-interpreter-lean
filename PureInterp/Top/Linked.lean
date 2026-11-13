import PureInterp.Machine.Loop
import PureInterp.Image.LinkIncluded
import PureInterp.Image.LinkTableEntries

/-!
# `Linked` holds of the real image

`Machine.Linked` bundles what `run_sim` assumes. Its fields are of two kinds:

* **static** facts, determined by the ELF: that each function the loop runs
  is part of the code, what the instruction table holds for the six supported
  opcodes, that every table entry is an even address, and the pc-relative
  equations (`auipc`/`addi` pairs computing the table address, `jal` targets).
  These are proved here for `Image.imageCode`, `Image.imageTable`,
  `Image.tableAddr` and the functions' addresses.
* **dynamic** facts about one execution's run-time layout: where the machine
  stack, the context, the operand stack and the bytecode buffer are, their
  alignment and accessibility, and the padding of the bytecode buffer.
  `Dyn` holds exactly these, plus the four equations that fix the layout's
  table and exit addresses to the image's.

`linked_image : Dyn L E code → Linked Image.imageCode L E code …` discharges
every static field; no static field is left as a hypothesis.
-/

namespace PureInterp.Top
open RiscvZkvm.Rv64 PureInterp.Machine

set_option maxRecDepth 100000

/-- The run-time layout facts `run_sim` needs, for the real image. -/
structure Dyn (L : Layout) (E : ExitEnv) (code : List Model.Byte) : Prop where
  /-- The layout's instruction table is the image's, at its address. -/
  tbl : L.tbl = Image.tableAddr
  table : L.table = Image.imageTable
  /-- The exit path's functions are the image's `Context::exit` and `longjmp`. -/
  be : E.be = Image.f_rt_Context_exit.addr
  bl : E.bl = Image.f_longjmp.addr
  /-- `slot2` is the `ra` slot of `Context::exit`'s frame, 24 bytes below the
      handlers' stack pointer; `fbase` is 80 bytes below that. -/
  slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2
  fbase : E.fbase + 80 = E.slot2
  /-- The operand stack and the context are doubleword-aligned. -/
  sal : L.bottom.toNat % 8 = 0
  ctxal : E.ctx.toNat % 8 = 0
  /-- The operand stack (1025 slots) ends at or below the context's result
      fields, and those fields do not wrap around the address space. -/
  below : L.bottom.toNat + 32 * 1025 ≤ E.ctx.toNat + 184
  ctxcover : E.ctx.toNat + 248 ≤ 2 ^ 64
  /-- The operand stack and the context's 64 result bytes are accessible. -/
  svalid : ∀ i, i < 32 * 1025 → isValidByteAccess (L.bottom + BitVec.ofNat 64 i) = true
  rvalid : ∀ i, i < 64 → isValidByteAccess (E.ctx + 184 + BitVec.ofNat 64 i) = true
  /-- The bytecode buffer is doubleword-aligned and holds 30 zero bytes, the
      code and at least 33 zero bytes; it does not wrap and is accessible. -/
  cal : L.codeBase.toNat % 8 = 0
  padded : ∃ pad, 33 ≤ pad ∧ L.code = List.replicate 30 0 ++ code ++ List.replicate pad 0
  cover : L.codeBase.toNat + L.code.length < 2 ^ 64
  cvalid : ∀ i, i < L.code.length → isValidByteAccess (L.codeBase + BitVec.ofNat 64 i) = true

/-- **The image satisfies the static part of `Linked`.** -/
theorem linked_image {L : Layout} {E : ExitEnv} {code : List Model.Byte} (D : Dyn L E code) :
    Linked Image.imageCode L E code Image.f_stop.addr Image.f_add.addr Image.f_sub.addr
      Image.f_pop.addr Image.f_push_1.addr Image.f_return.addr Image.f_invalid.addr
      Image.f_return_impl.addr Image.f_memmove.addr where
  cStop := Image.f_stop.included
  cAdd := Image.f_add.included
  cSub := Image.f_sub.included
  cPop := Image.f_pop.included
  cPush1 := Image.f_push_1.included
  cReturn := Image.f_return.included
  cReturnImpl := Image.f_return_impl.included
  cMemmove := Image.f_memmove.included
  cInvalid := Image.f_invalid.included
  cExit := by rw [D.be]; exact Image.f_rt_Context_exit.included
  cLongjmp := by rw [D.bl]; exact Image.f_longjmp.included
  tlen := by rw [D.table]; exact Image.imageTable_length
  tStop := by rw [D.table]; exact Image.imageTable_0x00
  tAdd := by rw [D.table]; exact Image.imageTable_0x01
  tSub := by rw [D.table]; exact Image.imageTable_0x03
  tPop := by rw [D.table]; exact Image.imageTable_0x50
  tPush1 := by rw [D.table]; exact Image.imageTable_0x60
  tReturn := by rw [D.table]; exact Image.imageTable_0xf3
  aligned := by rw [D.table]; exact Image.imageTable_aligned
  tblAdd := by rw [D.tbl]; link_eq
  tblSub := by rw [D.tbl]; link_eq
  tblPop := by rw [D.tbl]; link_eq
  tblPush1 := by rw [D.tbl]; link_eq
  eStop := by rw [D.be]; link_eq
  eInvalid := by rw [D.be]; link_eq
  eAddOog := by rw [D.be]; link_eq
  eAddErr := by rw [D.be]; link_eq
  eSubOog := by rw [D.be]; link_eq
  eSubErr := by rw [D.be]; link_eq
  ePopOog := by rw [D.be]; link_eq
  ePopErr := by rw [D.be]; link_eq
  ePushOog := by rw [D.be]; link_eq
  ePushOvf := by rw [D.be]; link_eq
  eReturnErr := by rw [D.be]; link_eq
  eReturnImpl := by link_eq
  eMemmove := by link_eq
  retAligned := by link_eq
  eReturnExit := by rw [D.be]; link_eq
  eLongjmp := by rw [D.be, D.bl]; link_eq
  slot2 := D.slot2
  fbase := D.fbase
  sal := D.sal
  ctxal := D.ctxal
  below := D.below
  ctxcover := D.ctxcover
  svalid := D.svalid
  rvalid := D.rvalid
  cal := D.cal
  padded := D.padded
  cover := D.cover
  cvalid := D.cvalid

end PureInterp.Top
