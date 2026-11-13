import PureInterp.Machine.Linked

/-!
# The simulation loop: the binary's handler loop computes `Model.run`
-/

namespace PureInterp.Machine
open RiscvZkvm.Rv64 PureInterp.Handlers

set_option maxRecDepth 100000

theorem step_other (code : List Model.Byte) (s : Model.State)
    (h0 : (Model.byteAt code s.pc).toNat ≠ 0x00) (h1 : (Model.byteAt code s.pc).toNat ≠ 0x01)
    (h1b : (Model.byteAt code s.pc).toNat ≠ 0x03)
    (h2 : (Model.byteAt code s.pc).toNat ≠ 0x50) (h3 : (Model.byteAt code s.pc).toNat ≠ 0x60)
    (h4 : (Model.byteAt code s.pc).toNat ≠ 0xf3) :
    Model.step code s = Model.failure := by
  unfold Model.step
  split <;> simp_all

variable {cr : CodeReq} {L : Layout} {E : ExitEnv} {code : List Model.Byte}
  {hS hA hB hP hU hR hI hRI hM : Word}

theorem run_sim (K : Linked cr L E code hS hA hB hP hU hR hI hRI hM) :
    ∀ (fuel : Nat) (s : Model.State) (r : Model.Result),
      Model.run code fuel s = some r → RunOK L hI code fuel s →
      ∀ (scr : Scratch) (limbs : List Word) (a1v g0 s2 st0 : Word) (res fr : List Word),
        Rep limbs s.stack → s.gas < 2 ^ 63 → s.pc ≤ code.length + 1 →
        res.length = 8 → fr.length = 10 →
        ∃ scr' limbs' j12 j13 j14 js2 status g res' fr', ResultOK r s.mem status g res res' ∧
          cpsTripleWithin (464 * fuel) (L.table.getD (Model.byteAt code s.pc).toNat 0)
            ((E.v0 + signExtend12 0x000#12) &&& ~~~1) cr
            (interp L scr limbs s.stack.length s.gas (30 + s.pc) ** exitFrame E a1v g0 s2 st0 res fr)
            (final L E scr' limbs' j12 j13 j14 js2 status g res' fr') := by
  intro fuel
  induction fuel with
  | zero => intro s r h; simp [Model.run] at h
  | succ n ih =>
    intro s r hrun hok scr limbs a1v g0 s2 st0 res fr hrep hgb hpc hresl hfrl
    obtain ⟨hop, hnext⟩ := hok
    have hlen := K.len
    have hcov := K.cover
    by_cases h0 : (Model.byteAt code s.pc).toNat = 0x00
    · -- STOP
      have hstep : Model.step code s = .halt ⟨.success, s.gas, []⟩ := by simp [Model.step, h0]
      simp only [Model.run, hstep, Option.some.injEq] at hrun
      subst hrun
      rw [h0, K.tStop]
      have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
        (stop_final cr L E scr limbs hS a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
            K.cStop K.cExit K.cLongjmp K.eStop K.eLongjmp K.slot2)
      exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inr ⟨st_0, s.gas, hgb, rfl, Or.inl ⟨rfl, rfl⟩⟩, T⟩
    have hpcl : s.pc < code.length := byteAt_ne_zero_lt code s.pc h0
    by_cases h1 : (Model.byteAt code s.pc).toNat = 0x01
    · -- ADD
      have hstep : Model.step code s = Model.charge s 3 (fun s => Model.binary s (· + ·)) := by
        simp [Model.step, h1]
      by_cases hg : s.gas < 3
      · have hf : Model.step code s = Model.failure := by rw [hstep]; simp [Model.charge, hg]
        simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
        subst hrun
        rw [h1, K.tAdd]
        have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
          (add_oog_final cr L E scr limbs hA a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
              K.cAdd K.cExit K.cLongjmp K.eAddOog K.eLongjmp K.slot2
              (charge_fail s.gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb hg))
        exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inr st_3⟩, T⟩
      · obtain ⟨hgas, _⟩ :=
          charge_ok s.gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb (by omega)
        by_cases hd : s.stack.length < 2
        · have hf : Model.step code s = Model.failure := by
            rw [hstep]
            rcases hst : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
            · simp [Model.charge, hg, Model.binary, hst, Model.failure]
            · simp [Model.charge, hg, Model.binary, hst, Model.failure]
            · exfalso
              have hd' := hd
              simp only [hst, List.length_cons] at hd'
              omega
          simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
          subst hrun
          rw [h1, K.tAdd]
          have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
            (add_err_final cr L E scr limbs hA a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
                K.cAdd K.cExit K.cLongjmp K.eAddErr K.eLongjmp K.slot2 hgas
                (depth2_fail L.bottom s.stack.length hd))
          exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inl st_2⟩, T⟩
        · obtain ⟨a, b, rest, hst⟩ : ∃ a b rest, s.stack = a :: b :: rest := by
            rcases hst : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
            · simp [hst] at hd
            · simp [hst] at hd
            · exact ⟨a, b, rest, rfl⟩
          have hstep' : Model.step code s =
              .next ⟨(a + b) :: rest, s.gas - 3, s.pc + 1, s.mem⟩ := by
            rw [hstep]; simp [Model.charge, hg, Model.binary, hst]
          simp only [Model.run, hstep'] at hrun
          simp only [hstep'] at hnext
          rw [hst] at hrep
          obtain ⟨scr1, limbs1, hrep1, T⟩ := add_step L scr limbs hA
            (L.table[(L.code[30 + s.pc + 1]'(by omega)).toNat]'(by
              have := (L.code[30 + s.pc + 1]'(by omega)).isLt; have := K.tlen; omega))
            a b rest s.gas (30 + s.pc) hrep (by omega) hgb K.cal (by omega) (by omega)
            (K.valid (30 + s.pc) 1 0x001#12 se_001 (by omega)) K.tlen K.tblAdd rfl
          obtain ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, T2⟩ :=
            ih ⟨(a + b) :: rest, s.gas - 3, s.pc + 1, s.mem⟩ r hrun hnext scr1 limbs1 a1v g0 s2 st0 res fr
              hrep1 (by show s.gas - 3 < 2 ^ 63; omega) (by show s.pc + 1 ≤ code.length + 1; omega) hresl hfrl
          refine ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, ?_⟩
          have T' := cpsTripleWithin_frameR (exitFrame E a1v g0 s2 st0 res fr)
            (exitFrame_pcFree E a1v g0 s2 st0 res fr) (cpsTripleWithin_extend_code K.cAdd T)
          rw [K.next (30 + s.pc + 1) (s.pc + 1) (by omega) (by omega)] at T'
          rw [h1, K.tAdd, hst]
          exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr T' T2)
    by_cases h1b : (Model.byteAt code s.pc).toNat = 0x03
    · -- SUB
      have hstep : Model.step code s = Model.charge s 3 (fun s => Model.binary s (· - ·)) := by
        simp [Model.step, h1b]
      by_cases hg : s.gas < 3
      · have hf : Model.step code s = Model.failure := by rw [hstep]; simp [Model.charge, hg]
        simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
        subst hrun
        rw [h1b, K.tSub]
        have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
          (sub_oog_final cr L E scr limbs hB a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
              K.cSub K.cExit K.cLongjmp K.eSubOog K.eLongjmp K.slot2
              (charge_fail s.gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb hg))
        exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inr st_3⟩, T⟩
      · obtain ⟨hgas, _⟩ :=
          charge_ok s.gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb (by omega)
        by_cases hd : s.stack.length < 2
        · have hf : Model.step code s = Model.failure := by
            rw [hstep]
            rcases hst : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
            · simp [Model.charge, hg, Model.binary, hst, Model.failure]
            · simp [Model.charge, hg, Model.binary, hst, Model.failure]
            · exfalso
              have hd' := hd
              simp only [hst, List.length_cons] at hd'
              omega
          simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
          subst hrun
          rw [h1b, K.tSub]
          have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
            (sub_err_final cr L E scr limbs hB a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
                K.cSub K.cExit K.cLongjmp K.eSubErr K.eLongjmp K.slot2 hgas
                (depth2_fail L.bottom s.stack.length hd))
          exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inl st_2⟩, T⟩
        · obtain ⟨a, b, rest, hst⟩ : ∃ a b rest, s.stack = a :: b :: rest := by
            rcases hst : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
            · simp [hst] at hd
            · simp [hst] at hd
            · exact ⟨a, b, rest, rfl⟩
          have hstep' : Model.step code s =
              .next ⟨(a - b) :: rest, s.gas - 3, s.pc + 1, s.mem⟩ := by
            rw [hstep]; simp [Model.charge, hg, Model.binary, hst]
          simp only [Model.run, hstep'] at hrun
          simp only [hstep'] at hnext
          rw [hst] at hrep
          obtain ⟨scr1, limbs1, hrep1, T⟩ := sub_step L scr limbs hB
            (L.table[(L.code[30 + s.pc + 1]'(by omega)).toNat]'(by
              have := (L.code[30 + s.pc + 1]'(by omega)).isLt; have := K.tlen; omega))
            a b rest s.gas (30 + s.pc) hrep (by omega) hgb K.cal (by omega) (by omega)
            (K.valid (30 + s.pc) 1 0x001#12 se_001 (by omega)) K.tlen K.tblSub rfl
          obtain ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, T2⟩ :=
            ih ⟨(a - b) :: rest, s.gas - 3, s.pc + 1, s.mem⟩ r hrun hnext scr1 limbs1 a1v g0 s2 st0 res fr
              hrep1 (by show s.gas - 3 < 2 ^ 63; omega) (by show s.pc + 1 ≤ code.length + 1; omega) hresl hfrl
          refine ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, ?_⟩
          have T' := cpsTripleWithin_frameR (exitFrame E a1v g0 s2 st0 res fr)
            (exitFrame_pcFree E a1v g0 s2 st0 res fr) (cpsTripleWithin_extend_code K.cSub T)
          rw [K.next (30 + s.pc + 1) (s.pc + 1) (by omega) (by omega)] at T'
          rw [h1b, K.tSub, hst]
          exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr T' T2)
    by_cases h2 : (Model.byteAt code s.pc).toNat = 0x50
    · -- POP
      by_cases hg : s.gas < 2
      · have hf : Model.step code s = Model.failure := by simp [Model.step, h2, Model.charge, hg]
        simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
        subst hrun
        rw [h2, K.tPop]
        have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
          (pop_oog_final cr L E scr limbs hP a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
            K.cPop K.cExit K.cLongjmp K.ePopOog K.eLongjmp K.slot2
            (charge_fail s.gas 2 0xffe#12 (by omega) (by omega) (by decide) hgb hg))
        exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inr st_3⟩, T⟩
      · obtain ⟨hgas, _⟩ :=
          charge_ok s.gas 2 0xffe#12 (by omega) (by omega) (by decide) hgb (by omega)
        rcases hst : s.stack with _ | ⟨a, rest⟩
        · have hf : Model.step code s = Model.failure := by
            simp [Model.step, h2, Model.charge, hg, hst]
          simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
          subst hrun
          have hl0 : s.stack.length = 0 := by rw [hst]; rfl
          have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
            (pop_err_final cr L E scr limbs hP a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
              K.cPop K.cExit K.cLongjmp K.ePopErr K.eLongjmp K.slot2 hgas
              (by rw [hl0]; exact depth1_fail L.bottom))
          rw [h2, K.tPop]
          rw [hl0] at T
          exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inl st_2⟩, T⟩
        · have hstep' : Model.step code s = .next ⟨rest, s.gas - 2, s.pc + 1, s.mem⟩ := by
            simp [Model.step, h2, Model.charge, hg, hst]
          simp only [Model.run, hstep'] at hrun
          simp only [hstep'] at hnext
          rw [hst] at hrep
          obtain ⟨scr1, hrep1, T⟩ := pop_step L scr limbs hP
            (L.table[(L.code[30 + s.pc + 1]'(by omega)).toNat]'(by
              have := (L.code[30 + s.pc + 1]'(by omega)).isLt; have := K.tlen; omega))
            a rest s.gas (30 + s.pc) hrep (by omega) hgb K.cal (by omega) (by omega)
            (K.valid (30 + s.pc) 1 0x001#12 se_001 (by omega)) K.tlen K.tblPop rfl
          obtain ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, T2⟩ :=
            ih ⟨rest, s.gas - 2, s.pc + 1, s.mem⟩ r hrun hnext scr1 limbs a1v g0 s2 st0 res fr
              hrep1 (by show s.gas - 2 < 2 ^ 63; omega) (by show s.pc + 1 ≤ code.length + 1; omega) hresl hfrl
          refine ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, ?_⟩
          have T' := cpsTripleWithin_frameR (exitFrame E a1v g0 s2 st0 res fr)
            (exitFrame_pcFree E a1v g0 s2 st0 res fr) (cpsTripleWithin_extend_code K.cPop T)
          rw [K.next (30 + s.pc + 1) (s.pc + 1) (by omega) (by omega)] at T'
          rw [h2, K.tPop]
          exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr T' T2)
    by_cases h3 : (Model.byteAt code s.pc).toNat = 0x60
    · -- PUSH1
      by_cases hg : s.gas < 3
      · have hf : Model.step code s = Model.failure := by simp [Model.step, h3, Model.charge, hg]
        simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
        subst hrun
        rw [h3, K.tPush1]
        have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
          (push1_oog_final cr L E scr limbs hU a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
            K.cPush1 K.cExit K.cLongjmp K.ePushOog K.eLongjmp K.slot2
            (charge_fail s.gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb hg))
        exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inr st_3⟩, T⟩
      · obtain ⟨hgas, _⟩ :=
          charge_ok s.gas 3 0xffd#12 (by omega) (by omega) (by decide) hgb (by omega)
        have hdep := hrep.depth
        by_cases hfull : s.stack.length ≥ 1024
        · have hf : Model.step code s = Model.failure := by
            simp [Model.step, h3, Model.charge, hg, Model.push, hfull]
          simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
          subst hrun
          rw [h3, K.tPush1]
          have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
            (push1_ovf_final cr L E scr limbs hU a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
              K.cPush1 K.cExit K.cLongjmp K.ePushOvf K.eLongjmp K.slot2 hgas
              (room_fail L.bottom s.stack.length (by omega)))
          exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inl st_2⟩, T⟩
        · have hstep' : Model.step code s =
              .next ⟨(Model.byteAt code (s.pc + 1)).zeroExtend 256 :: s.stack, s.gas - 3, s.pc + 2, s.mem⟩ := by
            simp [Model.step, h3, Model.charge, hg, Model.push, hfull]
          simp only [Model.run, hstep'] at hrun
          simp only [hstep'] at hnext
          obtain ⟨scr1, limbs1, hrep1, T⟩ := push1_step L scr limbs hU
            (L.table[(L.code[30 + s.pc + 2]'(by omega)).toNat]'(by
              have := (L.code[30 + s.pc + 2]'(by omega)).isLt; have := K.tlen; omega))
            s.stack s.gas (30 + s.pc) hrep (by omega) (by omega) hgb K.cal (by omega) (by omega)
            (K.valid (30 + s.pc) 1 0x001#12 se_001 (by omega)) (K.valid (30 + s.pc) 2 0x002#12 se_002 (by omega))
            K.tlen K.tblPush1 rfl
          rw [K.byte (30 + s.pc + 1) (s.pc + 1) (by omega) (by omega)] at hrep1
          obtain ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, T2⟩ :=
            ih ⟨(Model.byteAt code (s.pc + 1)).zeroExtend 256 :: s.stack, s.gas - 3, s.pc + 2, s.mem⟩
              r hrun hnext scr1 limbs1 a1v g0 s2 st0 res fr
              hrep1 (by show s.gas - 3 < 2 ^ 63; omega) (by show s.pc + 2 ≤ code.length + 1; omega) hresl hfrl
          refine ⟨scr', limbs', j12, j13, j14, js2, status, g, res', fr', hres, ?_⟩
          have T' := cpsTripleWithin_frameR (exitFrame E a1v g0 s2 st0 res fr)
            (exitFrame_pcFree E a1v g0 s2 st0 res fr) (cpsTripleWithin_extend_code K.cPush1 T)
          rw [K.next (30 + s.pc + 2) (s.pc + 2) (by omega) (by omega)] at T'
          rw [h3, K.tPush1]
          exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr T' T2)
    by_cases h4 : (Model.byteAt code s.pc).toNat = 0xf3
    · -- RETURN
      by_cases hd : s.stack.length < 2
      · have hf : Model.step code s = Model.failure := by
          rcases hst : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [Model.step, h4, hst]
          · simp [Model.step, h4, hst]
          · exfalso
            have hd' := hd
            simp only [hst, List.length_cons] at hd'
            omega
        simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
        subst hrun
        rw [h4, K.tReturn]
        have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
          (return_err_final cr L E scr limbs hR a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
            K.cReturn K.cExit K.cLongjmp K.eReturnErr K.eLongjmp K.slot2
            (depth2_fail L.bottom s.stack.length hd))
        exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inl st_2⟩, T⟩
      · obtain ⟨a, b, rest, hst⟩ : ∃ a b rest, s.stack = a :: b :: rest := by
          rcases hst : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [hst] at hd
          · simp [hst] at hd
          · exact ⟨a, b, rest, rfl⟩
        have hstep' : Model.step code s = .halt (Model.returnResult s.gas s.mem a b) := by
          simp [Model.step, h4, hst]
        simp only [Model.run, hstep', Option.some.injEq] at hrun
        subst hrun
        rw [hst] at hrep
        obtain ⟨scr', j12, j13, j14, js2, fr', T⟩ := return_final cr L E scr limbs hR hRI hM
          a1v g0 s2 st0 res fr a b rest s.gas (30 + s.pc) hrep hresl hfrl
          K.cReturn K.cReturnImpl K.cMemmove K.cExit K.cLongjmp K.eReturnImpl K.eMemmove
          K.retAligned K.eReturnExit K.eLongjmp K.slot2 K.fbase K.sal K.ctxal K.below K.ctxcover
          K.svalid K.rvalid
        rw [h4, K.tReturn, hst]
        exact ⟨scr', limbs, j12, j13, j14, js2, _, _, _, fr',
          Or.inr ⟨st_0, s.gas, hgb, rfl, Or.inr ⟨a, b, rfl, rfl⟩⟩,
          cpsTripleWithin_mono_nSteps (by omega) T⟩
    · -- any other opcode whose handler is `invalid`
      have hf := step_other code s h0 h1 h1b h2 h3 h4
      have hI' : L.table.getD (Model.byteAt code s.pc).toNat 0 = hI := by
        rcases hop with h | h | h | h | h | h | h
        · exact absurd h h0
        · exact absurd h h1
        · exact absurd h h1b
        · exact absurd h h2
        · exact absurd h h3
        · exact absurd h h4
        · exact h
      simp only [Model.run, hf, Model.failure, Option.some.injEq] at hrun
      subst hrun
      rw [hI']
      have T := cpsTripleWithin_mono_nSteps (nSteps' := 464 * (n + 1)) (by omega)
        (invalid_final cr L E scr limbs hI a1v g0 s2 st0 res fr s.stack.length s.gas (30 + s.pc)
          K.cInvalid K.cExit K.cLongjmp K.eInvalid K.eLongjmp K.slot2)
      exact ⟨_, _, _, _, _, _, _, _, _, _, Or.inl ⟨rfl, Or.inl st_2⟩, T⟩

end PureInterp.Machine
