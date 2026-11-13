import PureInterp.Machine.Fail
import PureInterp.Machine.ReturnFinal

/-!
# The simulation loop

`run_sim`: whenever the model halts within `fuel` instructions, the binary,
started at the handler of the current opcode in a state satisfying the
invariant, reaches the `setjmp` return site with the model's result in the
runtime context. `Linked` collects what must hold of the loaded image for
that: where each function is, what the instruction table contains, and how
the bytecode buffer was prepared.
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

/-- Facts about the loaded image and the prepared buffers. `hS`, `hA`, `hB`,
    `hP`, `hU`, `hR`, `hI` are the entry addresses of the STOP, ADD, SUB, POP,
    PUSH1, RETURN and invalid handlers; `hRI` and `hM` those of `return_impl`
    and `memmove`. -/
structure Linked (cr : CodeReq) (L : Layout) (E : ExitEnv) (code : List Model.Byte)
    (hS hA hB hP hU hR hI hRI hM : Word) : Prop where
  cStop : ∀ a i, CodeReq.ofProg hS Image.f_stop.prog a = some i → cr a = some i
  cAdd : ∀ a i, CodeReq.ofProg hA Image.f_add.prog a = some i → cr a = some i
  cSub : ∀ a i, CodeReq.ofProg hB Image.f_sub.prog a = some i → cr a = some i
  cPop : ∀ a i, CodeReq.ofProg hP Image.f_pop.prog a = some i → cr a = some i
  cPush1 : ∀ a i, CodeReq.ofProg hU Image.f_push_1.prog a = some i → cr a = some i
  cReturn : ∀ a i, CodeReq.ofProg hR Image.f_return.prog a = some i → cr a = some i
  cReturnImpl : ∀ a i, CodeReq.ofProg hRI Image.f_return_impl.prog a = some i → cr a = some i
  cMemmove : ∀ a i, CodeReq.ofProg hM Image.f_memmove.prog a = some i → cr a = some i
  cInvalid : ∀ a i, CodeReq.ofProg hI Image.f_invalid.prog a = some i → cr a = some i
  cExit : ∀ a i, CodeReq.ofProg E.be Image.f_rt_Context_exit.prog a = some i → cr a = some i
  cLongjmp : ∀ a i, CodeReq.ofProg E.bl Image.f_longjmp.prog a = some i → cr a = some i
  tlen : L.table.length = 256
  tStop : L.table.getD 0x00 0 = hS
  tAdd : L.table.getD 0x01 0 = hA
  tSub : L.table.getD 0x03 0 = hB
  tPop : L.table.getD 0x50 0 = hP
  tPush1 : L.table.getD 0x60 0 = hU
  tReturn : L.table.getD 0xf3 0 = hR
  aligned : ∀ i, i < 256 →
    (L.table.getD i 0 + signExtend12 0x000#12) &&& ~~~1 = L.table.getD i 0
  tblAdd : hA + (136 : Word) + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0x24c#12 = L.tbl
  tblSub : hB + (136 : Word) + (((0x1fffd#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0x30c#12 = L.tbl
  tblPop : hP + (28 : Word) + (((0x20000#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xca8#12 = L.tbl
  tblPush1 : hU + (56 : Word) + (((0x1fffa#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xd0c#12 = L.tbl
  eStop : hS + 16 + signExtend21 0x00acb8#21 = E.be
  eInvalid : hI + 16 + signExtend21 0x00accc#21 = E.be
  eAddOog : hA + 180 + signExtend21 0x007de4#21 = E.be
  eAddErr : hA + 188 + signExtend21 0x007ddc#21 = E.be
  eSubOog : hB + 180 + signExtend21 0x007ea4#21 = E.be
  eSubErr : hB + 188 + signExtend21 0x007e9c#21 = E.be
  ePopOog : hP + 72 + signExtend21 0x00a840#21 = E.be
  ePopErr : hP + 80 + signExtend21 0x00a838#21 = E.be
  ePushOog : hU + 100 + signExtend21 0x0048a4#21 = E.be
  ePushOvf : hU + 108 + signExtend21 0x00489c#21 = E.be
  eReturnErr : hR + 44 + signExtend21 0x0047f8#21 = E.be
  eReturnImpl : hR + 36 + signExtend21 0x1fff68#21 = hRI
  eMemmove : hRI + 88 + signExtend21 0x003860#21 = hM
  /-- `memmove` returns into `return_impl` at an even address. -/
  retAligned : (hRI + 88 + 4 + signExtend12 0x000#12) &&& ~~~1 = hRI + 92
  eReturnExit : hRI + 112 + signExtend21 0x004828#21 = E.be
  eLongjmp : E.be + 24 + signExtend21 0x000044#21 = E.bl
  slot2 : L.sp + signExtend12 0xff0#12 + signExtend12 0xff0#12 + signExtend12 0x008#12 = E.slot2
  fbase : E.fbase + 80 = E.slot2
  /-- The operand stack and the context are doubleword-aligned, the stack
      lies below the context's result fields (the context is on the machine
      stack, above every buffer), and their bytes are accessible. -/
  sal : L.bottom.toNat % 8 = 0
  ctxal : E.ctx.toNat % 8 = 0
  below : L.bottom.toNat + 32 * 1025 ≤ E.ctx.toNat + 184
  ctxcover : E.ctx.toNat + 248 ≤ 2 ^ 64
  svalid : ∀ i, i < 32 * 1025 → isValidByteAccess (L.bottom + BitVec.ofNat 64 i) = true
  rvalid : ∀ i, i < 64 → isValidByteAccess (E.ctx + 184 + BitVec.ofNat 64 i) = true
  cal : L.codeBase.toNat % 8 = 0
  /-- The buffer `Intercode` builds: 30 zero bytes, the code, and at least 33
      zero bytes. Code byte `pc` is buffer byte `30 + pc`. -/
  padded : ∃ pad, 33 ≤ pad ∧ L.code = List.replicate 30 0 ++ code ++ List.replicate pad 0
  cover : L.codeBase.toNat + L.code.length < 2 ^ 64
  cvalid : ∀ i, i < L.code.length → isValidByteAccess (L.codeBase + BitVec.ofNat 64 i) = true

/-- The opcode is one the loop theorem covers: one of the six implemented
    ones, or one whose table entry is the invalid handler. -/
def OpOK (L : Layout) (hI : Word) (b : Model.Byte) : Prop :=
  b.toNat = 0x00 ∨ b.toNat = 0x01 ∨ b.toNat = 0x03 ∨ b.toNat = 0x50 ∨ b.toNat = 0x60 ∨ b.toNat = 0xf3 ∨
    L.table.getD b.toNat 0 = hI

/-- Every opcode the run executes is covered. -/
def RunOK (L : Layout) (hI : Word) (code : List Model.Byte) : Nat → Model.State → Prop
  | 0, _ => True
  | fuel + 1, s =>
    OpOK L hI (Model.byteAt code s.pc) ∧
      match Model.step code s with
      | .halt _ => True
      | .next s' => RunOK L hI code fuel s'

/-- The context holds the model's result `r`. `mem` is the model's active
    memory size, `res0` the context's `result.offset`/`result.size` words when
    the loop was entered and `res` the same words at the end. Either the run
    failed and the status is 2 (error) or 3 (out of gas); or the status is 0,
    the gas field holds some `gas`, and
    * the result words are untouched and `r` is success with `gas` left and
      no output (STOP), or
    * the result words are the limbs of an offset and a size and `r` is
      `Model.returnResult gas mem off size` (RETURN). That function mirrors
      what `Context::copy_result_data` does with these fields after the
      interpreter has left; showing that the binary's code does so is part
      of the exit glue, not of the loop. -/
def ResultOK (r : Model.Result) (mem : Nat) (status g : Word) (res0 res : List Word) : Prop :=
  (r = ⟨.failure, 0, []⟩ ∧ (status = 2 ∨ status = 3)) ∨
  (status = 0 ∧ ∃ gas, gas < 2 ^ 63 ∧ g = BitVec.ofNat 64 gas ∧
    ((res = res0 ∧ r = ⟨.success, gas, []⟩) ∨
     (∃ off size : Model.Word256, res = limbsOf off ++ limbsOf size ∧
        r = Model.returnResult gas mem off size)))

theorem exitFrame_pcFree (E : ExitEnv) (a1v g0 s2 st0 : Word) (res fr : List Word) :
    (exitFrame E a1v g0 s2 st0 res fr).pcFree := by
  unfold exitFrame; pcFree

theorem st_0 : (0 : Word) + signExtend12 0x000#12 = 0 := by decide
theorem st_2 : (0 : Word) + signExtend12 0x002#12 = 2 := by decide
theorem st_3 : (0 : Word) + signExtend12 0x003#12 = 3 := by decide

/-- Too little gas makes the handlers' charge go negative. -/
theorem charge_fail (gas c : Nat) (imm : BitVec 12) (hc : c < 2048) (hpos : 0 < c)
    (himm : imm = BitVec.ofNat 12 (4096 - c)) (hg : gas < 2 ^ 63) (hlt : gas < c) :
    BitVec.slt (BitVec.ofNat 64 gas + signExtend12 imm) 0 := by
  have hn : (BitVec.ofNat 64 gas).toNat = gas := by simp; omega
  obtain ⟨h1, _⟩ := Refine.gas_charge (BitVec.ofNat 64 gas) c imm hc himm (by omega) hpos
  by_contra h
  have := h1.mp (by simpa using h)
  omega

theorem depth2_fail (bottom : Word) (n : Nat) (hn : n < 2) :
    ¬ BitVec.slt ((0 : Word) + signExtend12 0x020#12)
      (bottom + BitVec.ofNat 64 (32 * n) - bottom) := by
  have e1 : (0 : Word) + signExtend12 0x020#12 = BitVec.ofNat 64 32 := by decide
  have e2 : bottom + BitVec.ofNat 64 (32 * n) - bottom = BitVec.ofNat 64 (32 * n) := by bv_omega
  rw [e1, e2, BitVec.slt_iff_toInt_lt]
  simp [BitVec.toInt_eq_toNat_cond]
  omega

theorem depth1_fail (bottom : Word) :
    ¬ BitVec.slt (0 : Word) (bottom + BitVec.ofNat 64 (32 * 0) - bottom) := by
  have e2 : bottom + BitVec.ofNat 64 (32 * 0) - bottom = 0 := by bv_omega
  rw [e2]; decide

theorem room_fail (bottom : Word) (n : Nat) (hn : n = 1024) :
    BitVec.slt ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) (bottom + BitVec.ofNat 64 (32 * n) - bottom) := by
  subst hn
  have e1 : ((((0x00008#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 0xfe0#12) = BitVec.ofNat 64 32736 := by decide
  have e2 : bottom + BitVec.ofNat 64 (32 * 1024) - bottom = BitVec.ofNat 64 32768 := by bv_omega
  rw [e1, e2]; decide

section
variable {cr : CodeReq} {L : Layout} {E : ExitEnv} {code : List Model.Byte}
  {hS hA hB hP hU hR hI hRI hM : Word}

/-- Buffer byte `30 + i` is code byte `i`, zero past the end of the code. -/
theorem Linked.byte (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) (j i : Nat)
    (hj : j = 30 + i) (hi : j < L.code.length) :
    L.code[j] = Model.byteAt code i := by
  subst hj
  obtain ⟨pad, _, hp⟩ := K.padded
  unfold Model.byteAt
  have hg : L.code[30 + i]? = (List.replicate 30 0 ++ code ++ List.replicate pad 0)[30 + i]? := by
    rw [hp]
  rw [List.getElem?_eq_getElem hi, List.append_assoc,
    List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left] at hg
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < code.length
  · rw [List.getElem?_append_left h] at hg
    rw [← hg]; rfl
  · rw [List.getElem?_append_right (by omega)] at hg
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    have hl : L.code.length = 30 + code.length + pad := by simp [hp]; omega
    rw [List.getElem?_replicate, if_pos (by omega)] at hg
    exact (Option.some.inj hg)

theorem Linked.len (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) :
    30 + code.length + 33 ≤ L.code.length := by
  obtain ⟨pad, h, hp⟩ := K.padded
  simp [hp]; omega

/-- A handler's dispatch lands on the loop's entry for the next opcode. -/
theorem Linked.next (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) (j i : Nat)
    (hj : j = 30 + i) (hi : j < L.code.length) :
    (L.table[(L.code[j]).toNat]'(by have := (L.code[j]).isLt; have := K.tlen; omega) +
      signExtend12 0x000#12) &&& ~~~1 = L.table.getD (Model.byteAt code i).toNat 0 := by
  have hlt := (L.code[j]).isLt
  have hl : (L.code[j]).toNat < L.table.length := by have := K.tlen; omega
  have := K.aligned (L.code[j]).toNat (by omega)
  rw [← K.byte j i hj hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at this ⊢
  exact this

theorem Linked.valid (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) (pc k : Nat) (ok : BitVec 12)
    (hok : signExtend12 ok = BitVec.ofNat 64 k) (h : pc + k < L.code.length) :
    isValidByteAccess (L.codeBase + BitVec.ofNat 64 pc + signExtend12 ok) = true := by
  rw [hok, ofNat_add_ofNat]; exact K.cvalid _ h

end

theorem byteAt_ne_zero_lt (code : List Model.Byte) (i : Nat)
    (h : (Model.byteAt code i).toNat ≠ 0) : i < code.length := by
  by_contra hc
  apply h
  unfold Model.byteAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)]

end PureInterp.Machine
