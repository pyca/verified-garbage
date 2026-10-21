module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule

/-! # Equal declared schedules determine coprimality and prepared-result shape -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

theorem schedule_gcd_eq {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : schedule E eBytes pBytes rBytes = schedule E eBytes qBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false) :
    decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) := by
  have H := congrArg Sched.gbad same
  rw [schedule_exponent rClose rComposite, schedule_exponent sClose sComposite] at H
  have equal := congrArg Bool.not H
  simp only [Bool.not_not] at equal
  apply Bool.eq_iff_iff.mpr
  have iff := Bool.eq_iff_iff.mp equal
  simpa only [beq_iff_eq, decide_eq_true_eq] using iff

theorem schedule_shape_eq {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : schedule E eBytes pBytes rBytes = schedule E eBytes qBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false)
    (good : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) :
    shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length)) := by
  have gcdEq := schedule_gcd_eq same rClose sClose rComposite sComposite
  have goodRight : Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1 :=
    of_decide_eq_true (gcdEq.symm.trans (decide_eq_true good))
  have H := congrArg Sched.mr same
  rw [schedule_mr rClose rComposite good, schedule_mr sClose sComposite goodRight] at H
  exact H

end VG.Proof.RsaKeyGen.X86.Candidate
