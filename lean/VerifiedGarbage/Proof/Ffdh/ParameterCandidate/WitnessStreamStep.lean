module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream

/-! One physical witness draw, including rejected samples, in the shared tape model. -/

@[expose] public section
namespace VG.Proof.Ffdh.ParameterCandidate
open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

theorem checkWitnesses_step {w : Nat} (positive : 0 < witnessOctets w) (checks : Nat) (r : Rand) :
    checkWitnesses w (checks + 1) r =
      if witnessOctets w ≤ r.length then
        let a := Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1)
        if 2 ≤ a ∧ a < w - 1 then
          if mrRound w a then checkWitnesses w checks (r.drop (witnessOctets w))
          else some (false, r.drop (witnessOctets w))
        else checkWitnesses w (checks + 1) (r.drop (witnessOctets w))
      else none := by
  rw [checkWitnesses, drawWitness_eq positive]
  by_cases enough : witnessOctets w ≤ r.length
  · simp only [ite_eq_left enough]
    by_cases range : 2 ≤ Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1) ∧
        Spec.Rsa.os2ip (r.take (witnessOctets w)) % 2 ^ bitLength (w - 1) < w - 1
    · simp only [ite_eq_left range, bind, Option.bind_some]
    · simp only [ite_eq_right range]
      rfl
  · simp only [ite_eq_right enough, bind, Option.bind_none]

end VG.Proof.Ffdh.ParameterCandidate
