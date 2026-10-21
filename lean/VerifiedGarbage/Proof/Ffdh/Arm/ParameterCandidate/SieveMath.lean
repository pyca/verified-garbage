module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy

/-! The native table prefix is precisely RSA's requested-width sieve. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

theorem sieveAny_mono {value a b : Nat} (bound : a ≤ b) (hit : sieveAny value a = true) :
    sieveAny value b = true := by
  simp only [sieveAny, List.any_eq_true, List.mem_range] at hit ⊢
  obtain ⟨i, hi, divides⟩ := hit
  exact ⟨i, by omega, divides⟩

theorem sieveNext_progress {n value i : Nat} (more : i < trialCount n) :
    i < sieveNext n value i ∧ sieveNext n value i ≤ trialCount n := by
  unfold sieveNext
  split <;> omega

theorem sieveAny_rsa {value bits : Nat} (large : 8161 < value) :
    sieveAny value (trialCount ((bits+7)/8)) = Spec.RsaKeyGen.obviouslyComposite bits value := by
  by_cases small : bits ≤ 1024
  · have width : (bits+7)/8 ≤ 128 := by omega
    have same : Spec.RsaKeyGen.obviouslyComposite 1024 value =
        Spec.RsaKeyGen.obviouslyComposite bits value := by
      simp only [Spec.RsaKeyGen.obviouslyComposite, Spec.RsaKeyGen.trialPrimes,
        show ¬1024<bits by omega, show ¬1024<1024 by omega, ite_false]
    have table := VG.Proof.RsaKeyGen.trialAny_eq (w:=16) large
    simpa only [trialCount, width, ite_true, VG.Proof.RsaKeyGen.trialAny,
      show ¬17≤16 by omega, ite_false, Nat.reduceMul, sieveAny, same] using table
  · have width : ¬(bits+7)/8 ≤ 128 := by omega
    have same : Spec.RsaKeyGen.obviouslyComposite 1088 value =
        Spec.RsaKeyGen.obviouslyComposite bits value := by
      simp only [Spec.RsaKeyGen.obviouslyComposite, Spec.RsaKeyGen.trialPrimes,
        show 1024<bits by omega, show 1024<1088 by omega, ite_true]
    have table := VG.Proof.RsaKeyGen.trialAny_eq (w:=17) large
    simpa only [trialCount, width, ite_false, VG.Proof.RsaKeyGen.trialAny,
      show 17≤17 by omega, ite_true, Nat.reduceMul, sieveAny, same] using table

theorem sieve_shape {value bits : Nat} (large : 8161 < value) (odd : value%2=1) :
    (!(sieveAny value (trialCount ((bits+7)/8)))) =
      (Spec.Ffdh.primeShape value && !Spec.RsaKeyGen.obviouslyComposite bits value) := by
  rw [←sieveAny_rsa large, VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve large odd]
  change (!sieveAny value (trialCount ((bits+7)/8))) =
    ((!sieveAny value 53) && !sieveAny value (trialCount ((bits+7)/8)))
  by_cases hit : sieveAny value (trialCount ((bits+7)/8)) = true
  · simp only [hit, Bool.not_true, Bool.and_false]
  · have noHit := Bool.eq_false_iff.mpr hit
    have noSmall : sieveAny value 53 = false := by
      apply Bool.eq_false_iff.mpr
      intro small
      exact hit (sieveAny_mono (trialCount_lower _) small)
    simp only [noHit, noSmall, Bool.not_false, Bool.and_true]

end VG.Proof.Ffdh.Arm.ParameterCandidate
