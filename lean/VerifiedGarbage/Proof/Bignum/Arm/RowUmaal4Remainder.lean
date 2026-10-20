module

import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Restart
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Fusion
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4

/-! A public two-word remainder precedes the grouped four-word loop. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

private def cmpCount (s : State) : State := subFlags s (s.gpr .lr) 0
private def parityFour (s : State) : State :=
  let t := s.setReg .r3 (s.gpr .lr &&& 2)
  subFlags t (t.gpr .r3) 0

private theorem cmpCount_exec (s : State) :
    Exec isa (.block [.cmp .lr (.imm 0)]) s [] (cmpCount s) := by
  apply Exec.block_iff.mpr
  simp only [execBlock, isa, exec, Op2.eval, Option.map_some, addrs, List.map_nil, List.append_nil]
  rfl

private theorem parityFour_exec (s : State) :
    Exec isa (.block rowParity4) s [] (parityFour s) := by
  apply Exec.block_iff.mpr
  simp only [rowParity4, execBlock, isa, exec, Op2.eval, Option.map_some, addrs,
    List.map_nil, List.append_nil]
  rfl

private theorem parityFour_restart (s : State) : RowRestart s (parityFour s) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem cmpCount_agree (s : State) : NoFlags s (cmpCount s) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem cmpCount_nonzero (s : State) (positive : 0 < (s.gpr .lr).toNat) :
    eval .ne (cmpCount s) = some true := by
  change some (!((s.gpr .lr - 0#32) == 0#32)) = some true
  rw [BitVec.sub_zero]
  have neq : s.gpr .lr ≠ 0#32 := by
    intro eq
    rw [eq] at positive
    contradiction
  simp only [beq_eq_false_iff_ne.mpr neq, Bool.not_false]

private theorem maskEven (x : BitVec 32) (even : x.toNat % 2 = 0) :
    (x &&& 2 == 0) = decide (x.toNat % 4 = 0) := by
  have low : x &&& 3 = BitVec.ofNat 32 (x.toNat % 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (3 : BitVec 32).toNat = 3 from rfl,
      BitVec.toNat_ofNat]
    rw [show 3 = 2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have same : x &&& 2 = (x &&& 3) &&& 2 := by
    rw [BitVec.and_assoc]
    rfl
  rw [same,low]
  have cases : x.toNat % 4 = 0 ∨ x.toNat % 4 = 2 := by omega
  rcases cases with h | h <;> rw [h] <;> decide

private theorem cmpCount_terminal {s t : State} {tr : List Leak}
    (run : Exec isa (.block rowBodyU) s tr t) (zero : t.gpr .lr = 0) : cmpCount t = t := by
  obtain ⟨_,_,_,_,rfl,_⟩ := rowBodyU_forward run
  have count : (stepNew 4 (stepNew 0 s)).gpr .lr = 2 := by
    change (stepNew 4 (stepNew 0 s)).gpr .lr - 2 = 0 at zero
    simpa using BitVec.sub_eq_iff_eq_add.mp zero
  simp only [cmpCount, advState, subFlags, gpr_setReg, ↓reduceIte, count]
  rfl

private def remainderCode : Prog isa :=
  .seq (.ite .ne (.block rowBodyU) (.block []))
    (.seq (.block [.cmp .lr (.imm 0)])
      (.ite .ne (.loop (.block rowBodyU4) .ne) (.block [])))

private theorem remainder_sim {s t : State} {tr : List Leak}
    (positive : 0 < (s.gpr .lr).toNat) (even : (s.gpr .lr).toNat % 2 = 0)
    (parity : s.z = decide ((s.gpr .lr).toNat % 4 = 0))
    (run : Exec isa (.loop (.block rowBodyU) .ne) s tr t) :
    ∃ trace, Exec isa remainderCode s trace t := by
  by_cases rem : (s.gpr .lr).toNat % 4 = 0
  · have skip : Exec isa (.ite .ne (.block rowBodyU) (.block [])) s [.branch false] s :=
      .iteF (by change some (!s.z) = some false; simp [parity,rem]) (Exec.block_iff.mpr rfl)
    have count : (cmpCount s).gpr .lr = s.gpr .lr := rfl
    obtain ⟨trace, grouped⟩ := rowLoopU4_control rowFourFusion _ rfl positive rem (cmpCount_agree s) run
    have enter : Exec isa (.ite .ne (.loop (.block rowBodyU4) .ne) (.block [])) (cmpCount s) (.branch true :: trace) t :=
      .iteT (cmpCount_nonzero s positive) grouped
    exact ⟨_,.seq skip (.seq (cmpCount_exec s) enter)⟩
  · have remTwo : (s.gpr .lr).toNat % 4 = 2 := by omega
    have takePair : eval .ne s = some true := by simp [eval,parity,rem]
    cases run with
    | loopExit first exit =>
      have facts := rowBodyU_count_nat first (by omega)
      have last : t.z = true := by
        change some (!t.z) = some false at exit
        cases h : t.z <;> simp_all
      have countTwo := of_decide_eq_true (facts.2.symm.trans last)
      have zero : t.gpr .lr = 0 := BitVec.eq_of_toNat_eq (by simpa [countTwo] using facts.1)
      have cmpEq := cmpCount_terminal first zero
      have skipLoop : Exec isa (.ite .ne (.loop (.block rowBodyU4) .ne) (.block [])) t [.branch false] t :=
        .iteF (by change some (!t.z) = some false; simp [last]) (Exec.block_iff.mpr rfl)
      have cmp : Exec isa (.block [.cmp .lr (.imm 0)]) t [] t := by simpa only [cmpEq] using cmpCount_exec t
      exact ⟨_,.seq (.iteT takePair first) (.seq cmp skipLoop)⟩
    | loopNext first branch tail =>
      have facts := rowBodyU_count_nat first (by omega)
      rename_i u tr1 tr2
      have nonzero : u.z = false := by
        change some (!u.z) = some true at branch
        cases h : u.z <;> simp_all
      have notTwo := of_decide_eq_false (facts.2.symm.trans nonzero)
      have posU : 0 < (u.gpr .lr).toNat := by omega
      have modU : (u.gpr .lr).toNat % 4 = 0 := by omega
      obtain ⟨trace,grouped⟩ := rowLoopU4_control rowFourFusion _ rfl posU modU (cmpCount_agree u) tail
      have enter : Exec isa (.ite .ne (.loop (.block rowBodyU4) .ne) (.block [])) (cmpCount u) (.branch true :: trace) t :=
        .iteT (cmpCount_nonzero u posU) grouped
      exact ⟨_,.seq (.iteT takePair first) (.seq (cmpCount_exec u) enter)⟩

/-- The same complete row-loop endpoint, with four-word packets after a public remainder. -/
theorem rowLoopU_refine {s t : State} {tr : List Leak}
    (positive : 0 < (s.gpr .lr).toNat) (even : (s.gpr .lr).toNat % 2 = 0)
    (run : Exec isa rowLoopU s tr t) : ∃ trace, Exec isa rowLoopU4 s trace t := by
  cases run with
  | seq join rest =>
    cases rest with
    | seq loop finish =>
      rename_i a b trj trl trf
      have keep : a.gpr .lr = s.gpr .lr := Exec.gpr (h := join) (hn := Or.inl rfl) (by
        intro i hi; change i ∈ rowUJoin at hi
        simp only [rowUJoin,List.mem_cons,List.not_mem_nil,or_false] at hi
        subst i; rfl)
      have posA : 0 < (a.gpr .lr).toNat := by rw [keep]; exact positive
      have evenA : (a.gpr .lr).toNat % 2 = 0 := by rw [keep]; exact even
      have restart := rowLoopU_restart (parityFour_restart a) loop
      have posP : 0 < ((parityFour a).gpr .lr).toNat := posA
      have evenP : ((parityFour a).gpr .lr).toNat % 2 = 0 := evenA
      have parP : (parityFour a).z = decide (((parityFour a).gpr .lr).toNat % 4 = 0) := by
        change (((a.gpr .lr &&& 2#32) - 0#32) == 0#32) = decide ((a.gpr .lr).toNat % 4 = 0)
        rw [BitVec.sub_zero]
        exact maskEven (a.gpr .lr) evenA
      obtain ⟨trace,rem⟩ := remainder_sim posP evenP parP restart
      cases rem with
      | seq choose rest =>
        cases rest with
        | seq cmp grouped =>
          exact ⟨_, Exec.seq join (Exec.seq (parityFour_exec a)
            (Exec.seq choose (Exec.seq cmp (Exec.seq grouped finish))))⟩

end VG.Proof.Bignum.Arm
