module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.SievePattern
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput

/-! # The candidate contract's existing leak determines every permitted branch schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

def schedule (E : Environment) (eBytes pBytes entropy : List Byte) : Sched :=
  schedOf E.length (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy

def SameLeak (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) : Prop :=
  Spec.RsaKeyGen.candidateLeak E.length eBytes pBytes rBytes = Spec.RsaKeyGen.candidateLeak E.length eBytes qBytes sBytes

theorem schedule_eq {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ rBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) : schedule E eBytes pBytes rBytes = schedule E eBytes qBytes sBytes := by
  have L : 0 < E.length := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  exact schedOf_eq L length enough (by
    unfold SameLeak at leak
    simpa only [candidateLeak_eq, Spec.RsaKeyGen.candidateOp] using leak)

theorem schedule_close (E : Environment) (eBytes pBytes entropy : List Byte) :
    (schedule E eBytes pBytes entropy).close = Spec.RsaKeyGen.tooClose (8 * E.length)
      (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) := sched_close _ _ _ _

theorem schedule_composite {E : Environment} {eBytes pBytes entropy : List Byte}
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false) :
    (schedule E eBytes pBytes entropy).comp = Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) := sched_comp close

theorem schedule_exponent {E : Environment} {eBytes pBytes entropy : List Byte}
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = false) :
    (schedule E eBytes pBytes entropy).gbad = !(Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) == 1) :=
  sched_gbad close composite

theorem schedule_mr {E : Environment} {eBytes pBytes entropy : List Byte}
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = false)
    (gcd : Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) = 1) :
    (schedule E eBytes pBytes entropy).mr = shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length)) :=
  sched_mr close composite (by
    change (!(Nat.gcd (candidateValue E entropy - 1) (Spec.Rsa.os2ip eBytes) == 1)) = false
    rw [gcd]
    decide)

end VG.Proof.RsaKeyGen.X86.Candidate
