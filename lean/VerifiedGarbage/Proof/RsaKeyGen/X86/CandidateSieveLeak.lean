module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.SievePattern
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming

/-! # Rejected-candidate leakage permits the sieve pattern and passing candidates hide their values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

theorem candidate_op_composite {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte}
    (enough : E.length ≤ entropy.length)
    (close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) = false)
    (composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) = true) :
    Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy = some (.rejected, entropy.drop E.length) := by
  unfold Spec.RsaKeyGen.candidateOp
  rw [candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega), ite_t enough]
  change afterDraw (8 * E.length) (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes)
    (candidateValue E entropy) (entropy.drop E.length) = _
  simp only [afterDraw, close, composite, Bool.false_eq_true, Bool.not_true, Bool.false_and, ↓reduceIte]

theorem composite_candidates_eq {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rEnough : E.length ≤ rBytes.length) (sEnough : E.length ≤ sBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = true)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = true) :
    candidateValue E rBytes = candidateValue E sBytes := by
  unfold SameLeak at leak
  rw [candidateLeak_eq, candidateLeak_eq, candidate_op_composite v rEnough rClose rComposite,
    candidate_op_composite v sEnough sClose sComposite] at leak
  have rCount : rBytes.length - (rBytes.drop E.length).length = E.length := by rw [List.length_drop]; omega
  have sCount : sBytes.length - (sBytes.drop E.length).length = E.length := by rw [List.length_drop]; omega
  change 3 :: (rBytes.take (rBytes.length - (rBytes.drop E.length).length)).map (·.toNat) =
    3 :: (sBytes.take (sBytes.length - (sBytes.drop E.length).length)).map (·.toNat) at leak
  rw [rCount, sCount] at leak
  have bytes := map_toNat_inj (List.cons.inj leak).2
  unfold candidateValue
  rw [bytes]

theorem sieve_pattern {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rEnough : E.length ≤ rBytes.length) (sEnough : E.length ≤ sBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes) := by
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes)
  · have right := same.symm.trans composite
    have left := composite
    have bits : 64 * E.sieveGeometry.w = 8 * E.length := by change 64 * E.width = _; have := v.length_eq; omega
    apply Sieve.samePattern_passing rfl (candidate_large v rBytes) (candidate_large v sBytes)
    · rw [bits]; exact left
    · rw [bits]; exact right
  · rw [composite_candidates_eq v rEnough sEnough leak rClose sClose composite (same.symm.trans composite)]
    exact Sieve.samePattern_refl _ _

end VG.Proof.RsaKeyGen.X86.Candidate
