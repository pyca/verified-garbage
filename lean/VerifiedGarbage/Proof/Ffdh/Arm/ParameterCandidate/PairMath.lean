module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialOffsetMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

theorem pairAny_mono {value a b : Nat} (bound : a≤b) (hit : pairAny value a=true) :
    pairAny value b=true := by
  simp only [pairAny,List.any_eq_true,List.mem_range] at hit ⊢
  obtain ⟨i,hi,divides⟩ := hit
  exact ⟨i,by omega,divides⟩

theorem pairNext_progress {n value i : Nat} (more : i<trialCount n) :
    i<pairNext n value i ∧ pairNext n value i≤trialCount n := by
  unfold pairNext
  split <;> omega

theorem pairAny_eq {value count : Nat} (bound : count≤1024) (odd : value%2=1) :
    pairAny value count = (sieveAny value count || sieveAny ((value-1)/2) count) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pairAny,sieveAny,List.any_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq]
  have equivalent (i : Nat) (hi : i<count) :
      (VG.Impl.RsaKeyGen.tabEntry i-1+value)%VG.Impl.RsaKeyGen.tabEntry i=0 ↔
        ((value-1)/2)%VG.Impl.RsaKeyGen.tabEntry i=0 := by
    rw [Nat.add_comm]
    exact offset_divides_half odd (VG.Proof.RsaKeyGen.tabEntry_facts (by omega : i<1024)).1
  constructor
  · rintro ⟨i,hi,h|h⟩
    · exact Or.inl ⟨i,hi,h⟩
    · exact Or.inr ⟨i,hi,(equivalent i hi).mp h⟩
  · rintro (⟨i,hi,h⟩|⟨i,hi,h⟩)
    · exact ⟨i,hi,Or.inl h⟩
    · exact ⟨i,hi,Or.inr ((equivalent i hi).mpr h)⟩

theorem pair_shape {value bits : Nat} (largeP : 8161<value) (largeQ : 8161<(value-1)/2)
    (oddP : value%2=1) (oddQ : ((value-1)/2)%2=1) :
    (!pairAny value (trialCount ((bits+7)/8))) =
      ((Spec.Ffdh.primeShape value && !Spec.RsaKeyGen.obviouslyComposite bits value) &&
        (Spec.Ffdh.primeShape ((value-1)/2) && !Spec.RsaKeyGen.obviouslyComposite bits ((value-1)/2))) := by
  rw [←sieve_shape largeP oddP,←sieve_shape largeQ oddQ,pairAny_eq (trialCount_bound _) oddP]
  cases sieveAny value (trialCount ((bits+7)/8)) <;>
    cases sieveAny ((value-1)/2) (trialCount ((bits+7)/8)) <;> rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
