import PureInterp.Model
import PureInterp.Spec.Step
import PureInterp.Spec.Return

/-!
# The model agrees with EVMYulLean

The second arrow of `PureInterp/Model.lean`: a halting run of `Model.run` is matched by the
Yellow Paper loop `EVM.X`. Main results: `agrees` (any valid-jump set), `agrees_D_J` (in the
shape of `Model.AgreesWithSpec`) and `not_agreesWithSpec` (that proposition as stated is false,
witnessed by the one-byte code JUMPDEST).

Relative to `Model.AgreesWithSpec` the theorem assumes:

* `RunSupported`: every opcode byte the run executes is STOP, ADD, SUB, POP, PUSH1, RETURN, or a byte that
  EVMYulLean decodes to `INVALID` (0xfe and every byte that is no instruction). On the remaining
  bytes the model fails but EVMYulLean executes the instruction.
* `s.stack.length ≤ 1024`: `X` rejects an instruction that leaves more than 1024 words, so from
  a larger stack ADD and POP overflow in `X` while the model continues.
* `code.length + 1 < 2 ^ 256`: otherwise the specification's program counter wraps.
* For RETURN: the specification's active memory size is the model's, its memory holds only
  zeros, and `s.gas + cmem s.mem < cmem (2^23)` (see `Matches'.gasBound`).
-/

namespace PureInterp.Spec
open EvmYul EVM

/-! ## PUSH1 -/

theorem step_push1 (f c : ℕ) (st : EVM.State) (arg : UInt256) :
    EVM.step (f + 1) c (some (.Push .PUSH1, some (arg, 1))) st =
      .ok (EVM.State.replaceStackAndIncrPC
        { st with execLength := st.execLength + 1,
                  gasAvailable := st.gasAvailable - UInt256.ofNat c } (arg :: st.stack) 2) := by
  rfl

/-- One iteration of `X` on PUSH1. -/
theorem X_push1 (f : ℕ) (vj : Array UInt256) (s : EVM.State) (arg : UInt256)
    (hdec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (arg, 1)))
    (hgas : 3 ≤ s.gasAvailable.toNat) (hlen : s.stack.length + 1 ≤ 1024) :
    X (f + 2) vj s = X (f + 1) vj
      { s with stack := arg :: s.stack, pc := s.pc + .ofNat 2,
               execLength := s.execLength + 1,
               gasAvailable := s.gasAvailable - UInt256.ofNat 3 } := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hm : memoryExpansionCost s (.Push .PUSH1) = 0 := by
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t (.Push .PUSH1) = 3 := by
    intro t
    simp [C', GasConstants.Gverylow, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
      InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow,
      InstructionGasGroups.Wverylow.pushInstrsWithoutZero]
  have hg : ¬ s.gasAvailable.toNat < 3 := by omega
  have hl : ¬ (1024 < s.stack.length + 1) := by omega
  simp [hm, hc, δ, α, sub_ofNat_zero, hg, hl, Operation.isCreate]
  dsimp only [pure, Except.pure]
  rw [step_push1 f 3 _ arg]
  rfl

/-! ## Arithmetic on `UInt256` without wrap-around -/

theorem toNat_add_ofNat (a : UInt256) (k : ℕ) (h : a.toNat + k < 2 ^ 256) :
    (a + UInt256.ofNat k).toNat = a.toNat + k := by
  rcases a with ⟨v⟩
  show (v + Fin.ofNat _ k).val = v.val + k
  have hv : v.val + k < UInt256.size := Nat.lt_of_lt_of_eq h Refine.size_eq.symm
  rw [Fin.val_add]
  simp only [Fin.ofNat, Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt hv

theorem toNat_sub_ofNat (a : UInt256) (k : ℕ) (h : k ≤ a.toNat) :
    (a - UInt256.ofNat k).toNat = a.toNat - k := by
  rcases a with ⟨v⟩
  show (v - Fin.ofNat _ k).val = v.val - k
  have hv : v.val < UInt256.size := v.isLt
  have hk : k ≤ v.val := h
  have hk' : k % UInt256.size = k := Nat.mod_eq_of_lt (by omega)
  rw [Fin.sub_def]
  simp only [Fin.ofNat, hk']
  rw [show UInt256.size - k + v.val = (v.val - k) + UInt256.size by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_inj {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  rcases a with ⟨v⟩; rcases b with ⟨w⟩
  exact congrArg UInt256.mk (Fin.ext h)

/-! ## The model's code view and the specification's decoder -/

open Model (toByteArray)

theorem toList_loop (bs : ByteArray) (n i : ℕ) (r : List UInt8) (hn : bs.size - i = n) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction n generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop]
    have : ¬ i < bs.size := by omega
    have hd : bs.data.toList.drop i = [] := by
      apply List.drop_of_length_le
      simp only [Array.length_toList, ByteArray.size_data]; omega
    simp [this, hd]
  | succ n ih =>
    rw [ByteArray.toList.loop]
    have hi : i < bs.size := by omega
    rw [if_pos hi, ih (i + 1) _ (by omega)]
    have hi' : i < bs.data.toList.length := by
      simp only [Array.length_toList, ByteArray.size_data]; exact hi
    rw [List.drop_eq_getElem_cons hi']
    have : bs.get! i = bs.data.toList[i] := by
      rcases bs with ⟨d⟩
      have hd : i < d.size := hi
      simp [ByteArray.get!, hd]
    simp [this]

theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop bs _ 0 [] rfl]
  simp

theorem extract'_toList (a : ByteArray) (b e : ℕ) :
    (a.extract' b e).data.toList = (a.data.toList.drop b).take (e - b) := by
  unfold ByteArray.extract'
  split
  · rw [ByteArray.data_extract]
    simp [List.take_drop]
  · simp [toList_eq]

theorem get?_toByteArray (code : List Model.Byte) (n : ℕ) :
    (toByteArray code).get? n =
      if n < code.length then some (UInt8.ofNat (Model.byteAt code n).toNat) else none := by
  unfold ByteArray.get?
  have hs : (toByteArray code).size = code.length := by simp [toByteArray, ByteArray.size]
  by_cases h : n < code.length
  · rw [dif_pos (by rw [hs]; exact h), if_pos h]
    simp [toByteArray, Model.byteAt, ByteArray.get, h]
  · rw [dif_neg (by rw [hs]; exact h), if_neg h]

theorem lt_length_of_byteAt_ne {code : List Model.Byte} {n : ℕ} (h : (Model.byteAt code n).toNat ≠ 0) :
    n < code.length := by
  by_contra hn
  apply h
  simp [Model.byteAt, List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)]

theorem get?_of_byteAt {code : List Model.Byte} {n k : ℕ} (h : (Model.byteAt code n).toNat = k)
    (hk : k ≠ 0) : (toByteArray code).get? n = some (UInt8.ofNat k) := by
  rw [get?_toByteArray, if_pos (lt_length_of_byteAt_ne (by omega)), h]

theorem decode_add (code : List Model.Byte) (pc : UInt256) (h : (Model.byteAt code pc.toNat).toNat = 0x01) :
    decode (toByteArray code) pc = some (.ADD, none) := by
  unfold decode
  rw [get?_of_byteAt h (by decide)]
  rfl

theorem decode_sub (code : List Model.Byte) (pc : UInt256) (h : (Model.byteAt code pc.toNat).toNat = 0x03) :
    decode (toByteArray code) pc = some (.SUB, none) := by
  unfold decode
  rw [get?_of_byteAt h (by decide)]
  rfl

theorem decode_return (code : List Model.Byte) (pc : UInt256) (h : (Model.byteAt code pc.toNat).toNat = 0xf3) :
    decode (toByteArray code) pc = some (.RETURN, none) := by
  unfold decode
  rw [get?_of_byteAt h (by decide)]
  rfl

theorem decode_pop (code : List Model.Byte) (pc : UInt256) (h : (Model.byteAt code pc.toNat).toNat = 0x50) :
    decode (toByteArray code) pc = some (.POP, none) := by
  unfold decode
  rw [get?_of_byteAt h (by decide)]
  rfl

/-- INVALID (0xfe) and every byte that is no instruction: `parseInstr` maps them all to
    `INVALID`. -/
theorem decode_invalid (code : List Model.Byte) (pc : UInt256)
    (h : parseInstr (UInt8.ofNat (Model.byteAt code pc.toNat).toNat) = some .INVALID) :
    decode (toByteArray code) pc = some (.INVALID, none) := by
  have hne : (Model.byteAt code pc.toNat).toNat ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (by decide)
  unfold decode
  rw [get?_of_byteAt rfl hne]
  show (parseInstr (UInt8.ofNat (Model.byteAt code pc.toNat).toNat)).bind _ = _
  rw [h]
  rfl

/-- STOP, or past the end of the code, where `X` substitutes STOP. -/
theorem decode_stop (code : List Model.Byte) (pc : UInt256) (h : (Model.byteAt code pc.toNat).toNat = 0x00) :
    (decode (toByteArray code) pc).getD (.STOP, none) = (.STOP, none) := by
  by_cases hn : pc.toNat < code.length
  · unfold decode
    rw [get?_toByteArray, if_pos hn, h]
    rfl
  · simp [decode, get?_toByteArray, hn]

/-- The immediate of PUSH1 as the decoder builds it: the next code byte, or zero past the end. -/
theorem push1_arg (code : List Model.Byte) (n : ℕ) :
    uInt256OfByteArray ((toByteArray code).extract' (n + 1) (n + 1 + 1)) =
      Refine.u256 ((Model.byteAt code (n + 1)).zeroExtend 256) := by
  apply toNat_inj
  unfold uInt256OfByteArray
  rw [extract'_toList]
  simp only [Nat.add_sub_cancel_left, toByteArray, Model.byteAt, Refine.u256_toNat]
  by_cases hn : n + 1 < code.length
  · have hn' : n + 1 < (List.map (fun b : Model.Byte => UInt8.ofNat b.toNat) code).length := by
      simpa using hn
    rw [List.drop_eq_getElem_cons hn']
    have hb : code[n + 1].toNat < 256 := code[n + 1].isLt
    simp [fromBytes', UInt256.ofNat, UInt256.toNat, Id.run, hn, Refine.size_eq]
  · have hd : List.drop (n + 1) (List.map (fun b : Model.Byte => UInt8.ofNat b.toNat) code) = [] :=
      List.drop_of_length_le (by simpa using Nat.le_of_not_lt hn)
    rw [hd]
    simp [fromBytes', UInt256.ofNat, UInt256.toNat, Id.run,
      List.getElem?_eq_none (Nat.le_of_not_lt hn)]

theorem decode_push1 (code : List Model.Byte) (pc : UInt256)
    (h : (Model.byteAt code pc.toNat).toNat = 0x60) :
    decode (toByteArray code) pc =
      some (.Push .PUSH1, some (Refine.u256 ((Model.byteAt code (pc.toNat + 1)).zeroExtend 256), 1)) := by
  unfold decode
  rw [get?_of_byteAt h (by decide), ← push1_arg]
  rfl

/-! ## Gas and stack facts for the opcodes of the model -/

theorem mem_add (s : EVM.State) : memoryExpansionCost s .ADD = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
theorem mem_sub (s : EVM.State) : memoryExpansionCost s .SUB = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
theorem mem_pop (s : EVM.State) : memoryExpansionCost s .POP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
theorem mem_push1 (s : EVM.State) : memoryExpansionCost s (.Push .PUSH1) = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
theorem mem_invalid (s : EVM.State) : memoryExpansionCost s .INVALID = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem cost_add (t : EVM.State) : C' t .ADD = 3 := by
  simp [C', GasConstants.Gverylow, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow]
theorem cost_sub (t : EVM.State) : C' t .SUB = 3 := by
  simp [C', GasConstants.Gverylow, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow]
theorem cost_pop (t : EVM.State) : C' t .POP = 2 := by
  simp [C', GasConstants.Gbase, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
theorem cost_push1 (t : EVM.State) : C' t (.Push .PUSH1) = 3 := by
  simp [C', GasConstants.Gverylow, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow,
    InstructionGasGroups.Wverylow.pushInstrsWithoutZero]

/-! ## Exceptional halts of `X` -/

/-- Not enough gas for an instruction without memory expansion. -/
theorem X_outOfGas (f : ℕ) (vj : Array UInt256) (s : EVM.State) (w : Operation .EVM)
    (arg : Option (UInt256 × ℕ)) (c : ℕ)
    (hdec : decode s.executionEnv.code s.pc = some (w, arg))
    (hm : memoryExpansionCost s w = 0) (hc : ∀ t : EVM.State, C' t w = c)
    (hgas : s.gasAvailable.toNat < c) :
    X (f + 1) vj s = .error .OutOfGass := by
  rw [X]
  simp only [hdec, Option.getD_some]
  simp [hm, hc, sub_ofNat_zero, hgas]
  rfl

/-- Too few operands, with the gas check passed. -/
theorem X_underflow (f : ℕ) (vj : Array UInt256) (s : EVM.State) (w : Operation .EVM)
    (arg : Option (UInt256 × ℕ)) (c d : ℕ)
    (hdec : decode s.executionEnv.code s.pc = some (w, arg))
    (hm : memoryExpansionCost s w = 0) (hc : ∀ t : EVM.State, C' t w = c)
    (hgas : c ≤ s.gasAvailable.toNat) (hδ : δ w = some d) (hlen : s.stack.length < d) :
    X (f + 1) vj s = .error .StackUnderflow := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hg : ¬ s.gasAvailable.toNat < c := by omega
  simp [hm, hc, sub_ofNat_zero, hg, hδ, hlen]
  rfl

/-- PUSH1 onto a full stack. -/
theorem X_push1_overflow (f : ℕ) (vj : Array UInt256) (s : EVM.State) (arg : Option (UInt256 × ℕ))
    (hdec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, arg))
    (hgas : 3 ≤ s.gasAvailable.toNat) (hlen : 1024 ≤ s.stack.length) :
    X (f + 1) vj s = .error .StackOverflow := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hg : ¬ s.gasAvailable.toNat < 3 := by omega
  have hl : 1024 < s.stack.length + 1 := by omega
  simp [mem_push1, cost_push1, δ, α, sub_ofNat_zero, hg, hl]
  rfl

/-- INVALID (0xfe) is an exceptional halt whatever the gas. -/
theorem X_invalid (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (.INVALID, none)) :
    ∃ err, X (f + 1) vj s = .error err ∧ err ≠ .OutOfFuel := by
  rw [X]
  simp only [hdec, Option.getD_some]
  by_cases hg : s.gasAvailable.toNat < C' s .INVALID
  · refine ⟨.OutOfGass, ?_, fun h => by cases h⟩
    simp [mem_invalid, sub_ofNat_zero, hg]
    rfl
  · refine ⟨.InvalidInstruction, ?_, fun h => by cases h⟩
    simp [mem_invalid, sub_ofNat_zero, hg, δ]
    rfl

/-- `X` on STOP or past the end of the code. -/
theorem X_stop' (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, none) = (.STOP, none))
    (hlen : s.stack.length ≤ 1024) :
    ∃ e, X (f + 2) vj s = .ok (.success e .empty) ∧ e.gasAvailable = s.gasAvailable := by
  rw [X]
  simp only [hdec]
  have hm : memoryExpansionCost s .STOP = 0 := by simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t .STOP = 0 := by
    intro t
    simp [C', GasConstants.Gzero, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
      InstructionGasGroups.Wzero]
  have hl : ¬ (1024 < s.stack.length) := by omega
  simp [hm, hc, δ, α, sub_ofNat_zero, hl, Operation.isCreate, step_stop]
  exact ⟨_, rfl, sub_ofNat_zero _⟩

/-! ## The simulation -/

open Model (Result Outcome Matches ResultMatches)

/-- The opcode bytes on which the model and EVMYulLean agree: the six the model implements, and
    the bytes EVMYulLean decodes to `INVALID` (0xfe and the 107 bytes that are no instruction).
    On the other 144 bytes the model fails while EVMYulLean executes the instruction. -/
def Supported (b : Model.Byte) : Prop :=
  b.toNat = 0x00 ∨ b.toNat = 0x01 ∨ b.toNat = 0x03 ∨ b.toNat = 0x50 ∨ b.toNat = 0x60 ∨
    b.toNat = 0xf3 ∨
    parseInstr (UInt8.ofNat b.toNat) = some .INVALID

/-- Every opcode byte that a run of at most `fuel` instructions from `s` executes is
    `Supported`. Immediate bytes of PUSH1 are not constrained. -/
def RunSupported (code : List Model.Byte) : ℕ → Model.State → Prop
  | 0, _ => True
  | fuel + 1, s =>
    Supported (Model.byteAt code s.pc) ∧
      match Model.step code s with
      | .halt _ => True
      | .next s' => RunSupported code fuel s'

/-- `Model.Matches` with the invariants the simulation needs. -/
structure Matches' (c : List Model.Byte) (s : Model.State) (e : EVM.State) : Prop
    extends Matches c s e where
  /-- The Yellow Paper's stack limit; `X` rejects any instruction leaving more. -/
  stackLen : s.stack.length ≤ 1024
  /-- The program counter cannot wrap around `2^256`. -/
  codeLen : c.length + 1 < 2 ^ 256
  /-- The active memory size, in words. -/
  mem : e.activeWords.toNat = s.mem
  /-- Memory holds only zeros (no opcode of the model writes it). -/
  memZero : e.memory.data = Array.replicate e.memory.size 0
  /-- Gas is too little to pay for `2^23` words (256 MiB) of memory. Below
      that the binary's 28-bit bound on memory offsets, which the model has and
      the Yellow Paper lacks, cannot be told apart from running out of gas.
      The bound is `137464119296`; real gas limits are far smaller. -/
  gasBound : s.gas + Model.cmem s.mem < Model.cmem (2 ^ 23)

/-- What one model step demands of `X`. -/
def StepSim (code : List Model.Byte) (vj : Array UInt256) (e : EVM.State) : Outcome → Prop
  | .halt r => ∀ f, ResultMatches r (X (f + 2) vj e)
  | .next s' => ∃ e', Matches' code s' e' ∧ ∀ f, X (f + 2) vj e = X (f + 1) vj e'

theorem fail_sim (code : List Model.Byte) (vj : Array UInt256) (e : EVM.State)
    (h : ∀ f, ∃ err, X (f + 1) vj e = .error err ∧ err ≠ .OutOfFuel) :
    StepSim code vj e Model.failure := by
  intro f
  obtain ⟨err, hx, hne⟩ := h (f + 1)
  rw [hx]
  exact ⟨rfl, hne⟩

theorem step_sim (code : List Model.Byte) (vj : Array UInt256) (s : Model.State) (e : EVM.State)
    (hm : Matches' code s e) (hb : Supported (Model.byteAt code s.pc)) :
    StepSim code vj e (Model.step code s) := by
  have hcode := hm.code
  have hpc := hm.pc
  have hgas := hm.gas
  have hstk := hm.stack
  have hbyte : Model.byteAt code e.pc.toNat = Model.byteAt code s.pc := by rw [hpc]
  rcases hb with hb | hb | hb | hb | hb | hb | hb
  · -- STOP
    have hstep : Model.step code s = .halt ⟨.success, s.gas, []⟩ := by
      simp only [Model.step, hb]
    rw [hstep]
    intro f
    obtain ⟨e', hx, hg⟩ := X_stop' f vj e
      (by rw [hcode]; exact decode_stop code e.pc (by rw [hbyte]; exact hb))
      (by rw [hstk]; simpa using hm.stackLen)
    rw [hx]
    exact ⟨rfl, by rw [hg]; exact hgas, rfl⟩
  · -- ADD
    have hdec : decode e.executionEnv.code e.pc = some (.ADD, none) := by
      rw [hcode]; exact decode_add code e.pc (by rw [hbyte]; exact hb)
    have hlt : s.pc < code.length := lt_length_of_byteAt_ne (by omega)
    by_cases hg : s.gas < 3
    · have hstep : Model.step code s = Model.failure := by
        simp [Model.step, hb, Model.charge, hg]
      rw [hstep]
      exact fail_sim code vj e fun f =>
        ⟨_, X_outOfGas f vj e _ _ 3 hdec (mem_add e) cost_add (by omega), fun h => by cases h⟩
    · have hunder : s.stack.length < 2 → StepSim code vj e (Model.step code s) := by
        intro hl
        have hstep : Model.step code s = Model.failure := by
          rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [Model.step, hb, Model.charge, hg, Model.binary, hs]
          · simp [Model.step, hb, Model.charge, hg, Model.binary, hs]
          · rw [hs] at hl; simp only [List.length_cons] at hl; omega
        rw [hstep]
        exact fail_sim code vj e fun f =>
          ⟨_, X_underflow f vj e _ _ 3 2 hdec (mem_add e) cost_add (by omega) rfl
            (by rw [hstk]; simpa using hl), fun h => by cases h⟩
      rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact hunder (by rw [hs]; simp)
      · exact hunder (by rw [hs]; simp)
      · have hstep : Model.step code s =
            .next { stack := (a + b) :: rest, gas := s.gas - 3, pc := s.pc + 1, mem := s.mem } := by
          simp [Model.step, hb, Model.charge, hg, Model.binary, hs]
        have hsl := hm.stackLen
        rw [hs] at hsl
        simp only [List.length_cons] at hsl
        rw [hstep]
        refine ⟨{ e with stack := (Refine.u256 a + Refine.u256 b) :: rest.map Refine.u256,
                         pc := e.pc + .ofNat 1, execLength := e.execLength + 1,
                         gasAvailable := e.gasAvailable - UInt256.ofNat 3 },
          ⟨⟨hcode, by simp [Refine.u256_add], ?_, ?_⟩, by simpa using (by omega : rest.length + 1 ≤ 1024),
            hm.codeLen, hm.mem, hm.memZero, by have := hm.gasBound; show s.gas - 3 + Model.cmem s.mem < _; omega⟩,
          fun f => X_add f vj e _ _ _ hdec (by rw [hstk, hs]; rfl) (by omega) (by simpa using hsl)⟩
        · show (e.gasAvailable - UInt256.ofNat 3).toNat = s.gas - 3
          rw [toNat_sub_ofNat _ _ (by omega), hgas]
        · show (e.pc + UInt256.ofNat 1).toNat = s.pc + 1
          have := hm.codeLen
          rw [toNat_add_ofNat _ _ (by omega), hpc]
  · -- SUB
    have hdec : decode e.executionEnv.code e.pc = some (.SUB, none) := by
      rw [hcode]; exact decode_sub code e.pc (by rw [hbyte]; exact hb)
    have hlt : s.pc < code.length := lt_length_of_byteAt_ne (by omega)
    by_cases hg : s.gas < 3
    · have hstep : Model.step code s = Model.failure := by
        simp [Model.step, hb, Model.charge, hg]
      rw [hstep]
      exact fail_sim code vj e fun f =>
        ⟨_, X_outOfGas f vj e _ _ 3 hdec (mem_sub e) cost_sub (by omega), fun h => by cases h⟩
    · have hunder : s.stack.length < 2 → StepSim code vj e (Model.step code s) := by
        intro hl
        have hstep : Model.step code s = Model.failure := by
          rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [Model.step, hb, Model.charge, hg, Model.binary, hs]
          · simp [Model.step, hb, Model.charge, hg, Model.binary, hs]
          · rw [hs] at hl; simp only [List.length_cons] at hl; omega
        rw [hstep]
        exact fail_sim code vj e fun f =>
          ⟨_, X_underflow f vj e _ _ 3 2 hdec (mem_sub e) cost_sub (by omega) rfl
            (by rw [hstk]; simpa using hl), fun h => by cases h⟩
      rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact hunder (by rw [hs]; simp)
      · exact hunder (by rw [hs]; simp)
      · have hstep : Model.step code s =
            .next { stack := (a - b) :: rest, gas := s.gas - 3, pc := s.pc + 1, mem := s.mem } := by
          simp [Model.step, hb, Model.charge, hg, Model.binary, hs]
        have hsl := hm.stackLen
        rw [hs] at hsl
        simp only [List.length_cons] at hsl
        rw [hstep]
        refine ⟨{ e with stack := (Refine.u256 a - Refine.u256 b) :: rest.map Refine.u256,
                         pc := e.pc + .ofNat 1, execLength := e.execLength + 1,
                         gasAvailable := e.gasAvailable - UInt256.ofNat 3 },
          ⟨⟨hcode, by simp [Refine.u256_sub], ?_, ?_⟩, by simpa using (by omega : rest.length + 1 ≤ 1024),
            hm.codeLen, hm.mem, hm.memZero, by have := hm.gasBound; show s.gas - 3 + Model.cmem s.mem < _; omega⟩,
          fun f => X_sub f vj e _ _ _ hdec (by rw [hstk, hs]; rfl) (by omega) (by simpa using hsl)⟩
        · show (e.gasAvailable - UInt256.ofNat 3).toNat = s.gas - 3
          rw [toNat_sub_ofNat _ _ (by omega), hgas]
        · show (e.pc + UInt256.ofNat 1).toNat = s.pc + 1
          have := hm.codeLen
          rw [toNat_add_ofNat _ _ (by omega), hpc]
  · -- POP
    have hdec : decode e.executionEnv.code e.pc = some (.POP, none) := by
      rw [hcode]; exact decode_pop code e.pc (by rw [hbyte]; exact hb)
    have hlt : s.pc < code.length := lt_length_of_byteAt_ne (by omega)
    by_cases hg : s.gas < 2
    · have hstep : Model.step code s = Model.failure := by
        simp [Model.step, hb, Model.charge, hg]
      rw [hstep]
      exact fail_sim code vj e fun f =>
        ⟨_, X_outOfGas f vj e _ _ 2 hdec (mem_pop e) cost_pop (by omega), fun h => by cases h⟩
    · rcases hs : s.stack with _ | ⟨a, rest⟩
      · have hstep : Model.step code s = Model.failure := by
          simp [Model.step, hb, Model.charge, hg, hs]
        rw [hstep]
        exact fail_sim code vj e fun f =>
          ⟨_, X_underflow f vj e _ _ 2 1 hdec (mem_pop e) cost_pop (by omega) rfl
            (by rw [hstk, hs]; decide), fun h => by cases h⟩
      · have hstep : Model.step code s =
            .next { stack := rest, gas := s.gas - 2, pc := s.pc + 1, mem := s.mem } := by
          simp [Model.step, hb, Model.charge, hg, hs]
        have hsl := hm.stackLen
        rw [hs] at hsl
        simp only [List.length_cons] at hsl
        rw [hstep]
        refine ⟨{ e with stack := rest.map Refine.u256,
                         pc := e.pc + .ofNat 1, execLength := e.execLength + 1,
                         gasAvailable := e.gasAvailable - UInt256.ofNat 2 },
          ⟨⟨hcode, rfl, ?_, ?_⟩, by simpa using (by omega : rest.length ≤ 1024), hm.codeLen,
            hm.mem, hm.memZero, by have := hm.gasBound; show s.gas - 2 + Model.cmem s.mem < _; omega⟩,
          fun f => X_pop f vj e _ _ hdec (by rw [hstk, hs]; rfl) (by omega) (by simpa using hsl)⟩
        · show (e.gasAvailable - UInt256.ofNat 2).toNat = s.gas - 2
          rw [toNat_sub_ofNat _ _ (by omega), hgas]
        · show (e.pc + UInt256.ofNat 1).toNat = s.pc + 1
          have := hm.codeLen
          rw [toNat_add_ofNat _ _ (by omega), hpc]
  · -- PUSH1
    have hdec := decode_push1 code e.pc (by rw [hbyte]; exact hb)
    rw [← hcode, hpc] at hdec
    have hlt : s.pc < code.length := lt_length_of_byteAt_ne (by omega)
    by_cases hg : s.gas < 3
    · have hstep : Model.step code s = Model.failure := by
        simp [Model.step, hb, Model.charge, hg]
      rw [hstep]
      exact fail_sim code vj e fun f =>
        ⟨_, X_outOfGas f vj e _ _ 3 hdec (mem_push1 e) cost_push1 (by omega), fun h => by cases h⟩
    · have hel : e.stack.length = s.stack.length := by rw [hstk]; simp
      by_cases hfull : s.stack.length ≥ 1024
      · have hstep : Model.step code s = Model.failure := by
          simp [Model.step, hb, Model.charge, hg, Model.push, hfull]
        rw [hstep]
        exact fail_sim code vj e fun f =>
          ⟨_, X_push1_overflow f vj e _ hdec (by omega) (by omega), fun h => by cases h⟩
      · have hstep : Model.step code s =
            .next { stack := (Model.byteAt code (s.pc + 1)).zeroExtend 256 :: s.stack,
                    gas := s.gas - 3, pc := s.pc + 2, mem := s.mem } := by
          simp [Model.step, hb, Model.charge, hg, Model.push, hfull]
        rw [hstep]
        refine ⟨{ e with stack := Refine.u256 ((Model.byteAt code (s.pc + 1)).zeroExtend 256) :: e.stack,
                         pc := e.pc + .ofNat 2, execLength := e.execLength + 1,
                         gasAvailable := e.gasAvailable - UInt256.ofNat 3 },
          ⟨⟨hcode, by simp [hstk], ?_, ?_⟩, by simp; omega, hm.codeLen,
            hm.mem, hm.memZero, by have := hm.gasBound; show s.gas - 3 + Model.cmem s.mem < _; omega⟩,
          fun f => X_push1 f vj e _ hdec (by omega) (by omega)⟩
        · show (e.gasAvailable - UInt256.ofNat 3).toNat = s.gas - 3
          rw [toNat_sub_ofNat _ _ (by omega), hgas]
        · show (e.pc + UInt256.ofNat 2).toNat = s.pc + 2
          have := hm.codeLen
          rw [toNat_add_ofNat _ _ (by omega), hpc]
  · -- RETURN
    have hdec : decode e.executionEnv.code e.pc = some (.RETURN, none) := by
      rw [hcode]; exact decode_return code e.pc (by rw [hbyte]; exact hb)
    have hunder : s.stack.length < 2 → StepSim code vj e (Model.step code s) := by
      intro hl
      have hstep : Model.step code s = Model.failure := by
        rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · simp [Model.step, hb, hs]
        · simp [Model.step, hb, hs]
        · rw [hs] at hl; simp only [List.length_cons] at hl; omega
      rw [hstep]
      exact fail_sim code vj e fun f =>
        X_return_underflow f vj e hdec (by rw [hstk]; simpa using hl)
    rcases hs : s.stack with _ | ⟨off, _ | ⟨size, rest⟩⟩
    · exact hunder (by rw [hs]; simp)
    · exact hunder (by rw [hs]; simp)
    · have hstep : Model.step code s = .halt (Model.returnResult s.gas s.mem off size) := by
        simp [Model.step, hb, hs]
      have hsl := hm.stackLen
      rw [hs] at hsl
      simp only [List.length_cons] at hsl
      have hes : e.stack = Refine.u256 off :: Refine.u256 size :: rest.map Refine.u256 := by
        rw [hstk, hs]; rfl
      have hcost := memCost_return e _ _ _ hes
      rw [hm.mem, Refine.u256_toNat, Refine.u256_toNat] at hcost
      have hgb := hm.gasBound
      have hoff : off.toNat < 2 ^ 256 := off.isLt
      have hsize : size.toNat < 2 ^ 256 := size.isLt
      -- a range reaching `2^28` needs more gas than there is
      have hfar : 2 ^ 28 ≤ off.toNat + size.toNat → size.toNat ≠ 0 →
          e.gasAvailable.toNat < memoryExpansionCost e .RETURN := by
        intro hbig hne
        rw [hcost, if_neg hne, hgas]
        have h1 : Model.cmem (2 ^ 23) ≤
            Model.cmem (max s.mem ((off.toNat + size.toNat + 31) / 32)) :=
          cmem_mono (Nat.le_trans (by omega) (Nat.le_max_right _ _))
        omega
      have hfail : e.gasAvailable.toNat < memoryExpansionCost e .RETURN →
          StepSim code vj e (.halt ⟨.failure, 0, []⟩) := fun hlt =>
        fail_sim code vj e fun f => ⟨_, X_return_oog f vj e hdec hlt, fun h => by cases h⟩
      rw [hstep]
      unfold Model.returnResult
      split
      · exact hfail (hfar (by omega) (by omega))
      · split
        · -- empty output: no expansion
          next hz =>
          intro f
          have hc0 : memoryExpansionCost e .RETURN = 0 := by rw [hcost, if_pos hz]; omega
          obtain ⟨e', hx, hg⟩ := X_return f vj e _ _ _ hdec hes (by omega) (by simpa using hsl)
          rw [hx]
          refine ⟨rfl, by rw [hg, hc0, sub_ofNat_zero]; exact hgas, ?_⟩
          rw [Refine.u256_toNat, Refine.u256_toNat, hz,
            readWithPadding_zero _ hm.memZero _ _ (by decide)]
          exact (toByteArray_zeros 0).symm
        · next hz =>
          split
          · exact hfail (hfar (by omega) hz)
          · have hc : memoryExpansionCost e .RETURN =
                Model.cmem (max s.mem ((off.toNat + size.toNat + 31) / 32)) - Model.cmem s.mem := by
              rw [hcost, if_neg hz]
            dsimp only
            split
            · exact hfail (by rw [hc, hgas]; assumption)
            · next hge =>
              intro f
              obtain ⟨e', hx, hg⟩ := X_return f vj e _ _ _ hdec hes (by rw [hc, hgas]; omega)
                (by simpa using hsl)
              rw [hx]
              refine ⟨rfl, ?_, ?_⟩
              · rw [hg, toNat_sub_ofNat _ _ (by rw [hc, hgas]; omega), hc, hgas]
              · rw [Refine.u256_toNat, Refine.u256_toNat,
                  readWithPadding_zero _ hm.memZero _ _ (by omega)]
                exact (toByteArray_zeros _).symm
  · -- INVALID
    have hstep : Model.step code s = Model.failure := by
      unfold Model.step
      split
      · next h => rw [h] at hb; exact absurd hb (by decide)
      · next h => rw [h] at hb; exact absurd hb (by decide)
      · next h => rw [h] at hb; exact absurd hb (by decide)
      · next h => rw [h] at hb; exact absurd hb (by decide)
      · next h => rw [h] at hb; exact absurd hb (by decide)
      · next h => rw [h] at hb; exact absurd hb (by decide)
      · rfl
    rw [hstep]
    exact fail_sim code vj e fun f => X_invalid f vj e
      (by rw [hcode]; exact decode_invalid code e.pc (by rw [hbyte]; exact hb))

/-- **The model agrees with EVMYulLean on runs that execute only supported opcodes.** -/
theorem agrees (code : List Model.Byte) (vj : Array UInt256) (fuel : ℕ) (s : Model.State) (r : Result)
    (e : EVM.State) (hm : Matches' code s e) (hsup : RunSupported code fuel s)
    (hrun : Model.run code fuel s = some r) :
    ResultMatches r (X (fuel + 1) vj e) := by
  induction fuel generalizing s e with
  | zero => simp [Model.run] at hrun
  | succ fuel ih =>
    obtain ⟨hb, hrest⟩ := hsup
    have hsim := step_sim code vj s e hm hb
    rw [Model.run] at hrun
    cases hstep : Model.step code s with
    | halt r' =>
      rw [hstep] at hrun hsim
      cases hrun
      exact hsim fuel
    | next s' =>
      rw [hstep] at hrun hsim hrest
      obtain ⟨e', hm', hx⟩ := hsim
      rw [hx fuel]
      exact ih s' e' hm' hrest hrun

/-- `agrees` in the shape of `Model.AgreesWithSpec`, with the added hypotheses. -/
theorem agrees_D_J (code : List Model.Byte) (fuel : ℕ) (s : Model.State) (r : Result)
    (e : EVM.State) (hm : Matches code s e) (hstack : s.stack.length ≤ 1024)
    (hlen : code.length + 1 < 2 ^ 256) (hmem : e.activeWords.toNat = s.mem)
    (hzero : e.memory.data = Array.replicate e.memory.size 0)
    (hgas : s.gas + Model.cmem s.mem < Model.cmem (2 ^ 23)) (hsup : RunSupported code fuel s)
    (hrun : Model.run code fuel s = some r) :
    ResultMatches r (X (fuel + 1) (D_J (toByteArray code) ⟨0⟩) e) :=
  agrees code _ fuel s r e ⟨hm, hstack, hlen, hmem, hzero, hgas⟩ hsup hrun

theorem step_jumpdest (f c : ℕ) (st : EVM.State) :
    EVM.step (f + 1) c (some (.JUMPDEST, none)) st =
      .ok (EVM.State.incrPC
        { st with execLength := st.execLength + 1,
                  gasAvailable := st.gasAvailable - UInt256.ofNat c }) := by
  rfl

/-- One iteration of `X` on JUMPDEST, an instruction the model does not implement. -/
theorem X_jumpdest (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (.JUMPDEST, none))
    (hgas : 1 ≤ s.gasAvailable.toNat) (hlen : s.stack.length ≤ 1024) :
    X (f + 2) vj s = X (f + 1) vj
      { s with pc := s.pc + .ofNat 1, execLength := s.execLength + 1,
               gasAvailable := s.gasAvailable - UInt256.ofNat 1 } := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hm : memoryExpansionCost s .JUMPDEST = 0 := by
    simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t .JUMPDEST = 1 := by
    intro t
    simp [C', GasConstants.Gjumpdest]
  have hg : ¬ s.gasAvailable.toNat < 1 := by omega
  have hl : ¬ (1024 < s.stack.length) := by omega
  simp [hm, hc, δ, α, sub_ofNat_zero, hg, hl, Operation.isCreate]
  dsimp only [pure, Except.pure]
  rw [step_jumpdest f 1 _]
  rfl

/-- `Model.AgreesWithSpec` is false as stated: on JUMPDEST followed by the end of the code the
    model fails, while `X` executes JUMPDEST and then stops successfully. -/
theorem not_agreesWithSpec : ¬ Model.AgreesWithSpec := by
  intro h
  let e : EVM.State :=
    { (default : EVM.State) with
      executionEnv := { (default : EVM.State).executionEnv with code := toByteArray [0x5b] },
      pc := ⟨0⟩, stack := [], gasAvailable := ⟨1⟩ }
  have hm : Matches [0x5b] (Model.init 1) e := ⟨rfl, rfl, rfl, rfl⟩
  have hr := h [0x5b] 2 (Model.init 1) ⟨.failure, 0, []⟩ e hm rfl
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hd : decode e.executionEnv.code e.pc = some (.JUMPDEST, none) := by
    show decode (toByteArray [0x5b]) (⟨0⟩ : UInt256) = _
    unfold decode
    rw [get?_toByteArray, h0, if_pos (by decide)]
    rfl
  rw [X_jumpdest 1 _ e hd (by decide) (by decide)] at hr
  have h1 : ((⟨0⟩ : UInt256) + UInt256.ofNat 1).toNat = 1 := by
    rw [toNat_add_ofNat _ _ (by rw [h0]; decide), h0]
  obtain ⟨e', hx, -⟩ := X_stop' 0 (D_J (toByteArray [0x5b]) ⟨0⟩)
    { e with pc := e.pc + .ofNat 1, execLength := e.execLength + 1,
             gasAvailable := e.gasAvailable - UInt256.ofNat 1 }
    (by
      show (decode (toByteArray [0x5b]) ((⟨0⟩ : UInt256) + UInt256.ofNat 1)).getD _ = _
      unfold decode
      rw [get?_toByteArray, h1, if_neg (by decide)]
      rfl)
    (by decide)
  rw [hx] at hr
  exact absurd hr.1 (by decide)

end PureInterp.Spec
