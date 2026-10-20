module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape

/-! # Every constructed p is odd and fits its fixed-width public buffer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem PSearchPlan.value_shape (P : PSearchPlan) (counter : Nat)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    P.value counter < 256 ^ P.context.geometry.pLen ∧ P.value counter % 2 = 1 := by
  have pw := P.context.geometry.width
  rw [P.seedLength] at hashSize
  unfold PSearchPlan.value
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega : 2 ≤ 8 * P.context.geometry.pLen) hashSize]
  dsimp only
  have shape := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (by omega : 2 ≤ 8 * P.context.geometry.pLen)
    (VG.Proof.Dsa.Generation.contributions (8 * P.context.geometry.qLen)
      (VG.Proof.Dsa.Generation.pDigest (8 * P.context.geometry.qLen) P.seed.bytes (1 + counter * (P.context.geometry.contributionCount + 1)))
      ((8 * P.context.geometry.pLen - 1) / (8 * P.context.geometry.qLen) + 1))
  refine ⟨?_, VG.Proof.Dsa.Generation.pReduction_odd _ _⟩
  have bound := Nat.lt_of_le_of_lt (VG.Proof.Dsa.Generation.pReduction_le (q := P.qvalue) shape.1).2 shape.2.2
  rw [Nat.pow_mul] at bound
  exact bound

theorem PSearchPlan.remaining_step (P : PSearchPlan) {counter used : Nat} (bound : counter < 32 * P.context.geometry.pLen) :
    P.remaining counter used =
      if P.value counter < 2 ^ (8 * P.context.geometry.pLen - 1) then P.remaining (counter + 1) used
      else match Spec.Dsa.probablePrime (P.value counter) (P.context.witnesses.bytes.drop used) with
        | none => none
        | some (accepted, rest) =>
          if accepted then some (some (P.value counter), rest)
          else VG.Proof.Dsa.Generation.primeSearch (8 * P.context.geometry.pLen) (8 * P.context.geometry.qLen)
            P.qvalue P.seed.bytes (counter + 1) rest :=
  VG.Proof.Dsa.Generation.primeSearch_step _ _ (by omega)
end VG.Proof.Dsa.X86.Generation
