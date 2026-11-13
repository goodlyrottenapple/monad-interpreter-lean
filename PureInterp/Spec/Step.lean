import EvmYul.EVM.Semantics

/-!
# One-instruction lemmas for the specification

EVMYulLean's `EVM.X` is the Yellow Paper's execution loop. Each lemma here
unfolds one iteration of `X` for one opcode under the conditions in which the
instruction succeeds, so the machine-code proofs never unfold `X` themselves.
-/

namespace PureInterp.Spec
open EvmYul EVM

/-- `EVM.step` on ADD: charge the gas, bump the step counter, apply the binary
    operation. -/
theorem step_add (f c : ℕ) (st : EVM.State) :
    EVM.step (f + 1) c (some (.ADD, none)) st =
      EVM.execBinOp UInt256.add
        { st with execLength := st.execLength + 1,
                  gasAvailable := st.gasAvailable - UInt256.ofNat c } := by
  rfl

theorem sub_ofNat_zero (g : UInt256) : g - UInt256.ofNat 0 = g := by
  rcases g with ⟨v⟩
  show UInt256.sub _ _ = _
  simp [UInt256.sub, UInt256.ofNat, Id.run]

/-- One iteration of the Yellow Paper's `X` on ADD. -/
theorem X_add (f : ℕ) (vj : Array UInt256) (s : EVM.State) (a b : UInt256) (rest : List UInt256)
    (hdec : decode s.executionEnv.code s.pc = some (.ADD, none))
    (hst : s.stack = a :: b :: rest) (hgas : 3 ≤ s.gasAvailable.toNat)
    (hlen : rest.length + 2 ≤ 1024) :
    X (f + 2) vj s = X (f + 1) vj
      { s with stack := (a + b) :: rest, pc := s.pc + .ofNat 1,
               execLength := s.execLength + 1,
               gasAvailable := s.gasAvailable - UInt256.ofNat 3 } := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hm : memoryExpansionCost s .ADD = 0 := by simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t .ADD = 3 := by
    intro t
    simp [C', GasConstants.Gverylow, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
      InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow]
  have hg3 : ¬ s.gasAvailable.toNat < 3 := by omega
  have hl : ¬ (1024 < rest.length + 1) := by omega
  have hu : ¬ (rest.length + 1 + 1 < 2) := by omega
  simp [hm, hc, δ, α, hst, sub_ofNat_zero, hg3, hl, hu, Operation.isCreate, step_add, execBinOp,
    Stack.pop2]
  rfl


/-- `EVM.step` on SUB: charge the gas, bump the step counter, apply the binary
    operation. -/
theorem step_sub (f c : ℕ) (st : EVM.State) :
    EVM.step (f + 1) c (some (.SUB, none)) st =
      EVM.execBinOp UInt256.sub
        { st with execLength := st.execLength + 1,
                  gasAvailable := st.gasAvailable - UInt256.ofNat c } := by
  rfl

/-- One iteration of the Yellow Paper's `X` on SUB. -/
theorem X_sub (f : ℕ) (vj : Array UInt256) (s : EVM.State) (a b : UInt256) (rest : List UInt256)
    (hdec : decode s.executionEnv.code s.pc = some (.SUB, none))
    (hst : s.stack = a :: b :: rest) (hgas : 3 ≤ s.gasAvailable.toNat)
    (hlen : rest.length + 2 ≤ 1024) :
    X (f + 2) vj s = X (f + 1) vj
      { s with stack := (a - b) :: rest, pc := s.pc + .ofNat 1,
               execLength := s.execLength + 1,
               gasAvailable := s.gasAvailable - UInt256.ofNat 3 } := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hm : memoryExpansionCost s .SUB = 0 := by simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t .SUB = 3 := by
    intro t
    simp [C', GasConstants.Gverylow, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
      InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow]
  have hg3 : ¬ s.gasAvailable.toNat < 3 := by omega
  have hl : ¬ (1024 < rest.length + 1) := by omega
  have hu : ¬ (rest.length + 1 + 1 < 2) := by omega
  simp [hm, hc, δ, α, hst, sub_ofNat_zero, hg3, hl, hu, Operation.isCreate, step_sub, execBinOp,
    Stack.pop2]
  rfl



theorem step_pop (f c : ℕ) (st : EVM.State) (a : UInt256) (rest : List UInt256)
    (h : st.stack = a :: rest) :
    EVM.step (f + 1) c (some (.POP, none)) st =
      .ok (EVM.State.replaceStackAndIncrPC
        { st with execLength := st.execLength + 1,
                  gasAvailable := st.gasAvailable - UInt256.ofNat c } rest) := by
  have e : EVM.step (f + 1) c (some (.POP, none)) st =
      (match st.stack.pop with
        | some ⟨stk, _⟩ => .ok <|
            EVM.State.replaceStackAndIncrPC
              { st with execLength := st.execLength + 1,
                        gasAvailable := st.gasAvailable - UInt256.ofNat c } stk
        | _ => .error .StackUnderflow) := rfl
  rw [e, h]
  rfl

/-- One iteration of `X` on POP. -/
theorem X_pop (f : ℕ) (vj : Array UInt256) (s : EVM.State) (a : UInt256) (rest : List UInt256)
    (hdec : decode s.executionEnv.code s.pc = some (.POP, none))
    (hst : s.stack = a :: rest) (hgas : 2 ≤ s.gasAvailable.toNat)
    (hlen : rest.length + 1 ≤ 1024) :
    X (f + 2) vj s = X (f + 1) vj
      { s with stack := rest, pc := s.pc + .ofNat 1,
               execLength := s.execLength + 1,
               gasAvailable := s.gasAvailable - UInt256.ofNat 2 } := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hm : memoryExpansionCost s .POP = 0 := by simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t .POP = 2 := by
    intro t
    simp [C', GasConstants.Gbase, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
      InstructionGasGroups.Wzero, InstructionGasGroups.Wbase]
  have hg : ¬ s.gasAvailable.toNat < 2 := by omega
  have hl : ¬ (1024 < rest.length) := by omega
  simp [hm, hc, δ, α, hst, sub_ofNat_zero, hg, hl, Operation.isCreate]
  dsimp only [pure, Except.pure]
  rw [step_pop f 2 _ a rest rfl]
  rfl

theorem step_stop (f c : ℕ) (st : EVM.State) :
    EVM.step (f + 1) c (some (.STOP, none)) st =
      .ok { st with execLength := st.execLength + 1,
                    gasAvailable := st.gasAvailable - UInt256.ofNat c,
                    returnData := .empty } := by
  rfl

/-- `X` on STOP: success with empty output and the gas untouched. -/
theorem X_stop (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (.STOP, none))
    (hlen : s.stack.length ≤ 1024) :
    ∃ e, X (f + 2) vj s = .ok (.success e .empty) ∧ e.gasAvailable = s.gasAvailable := by
  rw [X]
  simp only [hdec, Option.getD_some]
  have hm : memoryExpansionCost s .STOP = 0 := by simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have hc : ∀ t : EVM.State, C' t .STOP = 0 := by
    intro t
    simp [C', GasConstants.Gzero, InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
      InstructionGasGroups.Wzero]
  have hl : ¬ (1024 < s.stack.length) := by omega
  simp [hm, hc, δ, α, sub_ofNat_zero, hl, Operation.isCreate, step_stop]
  exact ⟨_, rfl, sub_ofNat_zero _⟩

end PureInterp.Spec
