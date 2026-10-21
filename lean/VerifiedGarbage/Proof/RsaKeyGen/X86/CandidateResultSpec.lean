module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedResult
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec

/-! # Native candidate results agree with the shared candidate operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

def StepOutputs (E : Environment) (entropy : List Byte)
    (result : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)) (s : State) : Prop :=
  match result with
  | none => Outputs E 0 0 (List.replicate E.length 0) s
  | some (.prime c, rest) => Outputs E 1 (entropy.length - rest.length) (Spec.Rsa.i2osp c E.length) s
  | some (.close, rest) => Outputs E 2 (entropy.length - rest.length) (List.replicate E.length 0) s
  | some (.rejected, rest) => Outputs E 3 (entropy.length - rest.length) (List.replicate E.length 0) s

theorem filtered_outputs_eq {E : Environment} (e : Nat) (p : Option Nat) (entropy : List Byte)
    (enough : E.length ≤ entropy.length) (s : State) :
    FilteredOutputs E e p entropy s ↔ StepOutputs E entropy
      (VG.Proof.RsaKeyGen.afterDraw (8 * E.length) e p (candidateValue E entropy) (entropy.drop E.length)) s := by
  have count : entropy.length - (entropy.length - E.length) = E.length := by omega
  unfold FilteredOutputs SieveOutputs ExponentOutputs VG.Proof.RsaKeyGen.afterDraw
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) p (candidateValue E entropy)
  · cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · by_cases gcd : Nat.gcd (candidateValue E entropy - 1) e = 1
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq, gcd]
        unfold PrimalityOutputs
        cases test : Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length) with
        | none => rfl
        | some pr => obtain ⟨prime, rest⟩ := pr; cases prime <;> rfl
      · simp [gcd, StepOutputs, count]
    · simp [StepOutputs, count]
  · simp [StepOutputs, count]

theorem candidate_outputs_eq {E : Environment} (v : E.Valid) (eBytes pBytes entropy : List Byte)
    (enough : E.length ≤ entropy.length) (s : State) :
    FilteredOutputs E (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy s ↔
      StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) s := by
  unfold Spec.RsaKeyGen.candidateOp
  rw [VG.Proof.RsaKeyGen.candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega)]
  rw [VG.Proof.RsaKeyGen.ite_t enough]
  simpa only [candidateValue, VG.Proof.RsaKeyGen.seg, List.drop_zero] using
    filtered_outputs_eq (E := E) (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy enough s

end VG.Proof.RsaKeyGen.X86.Candidate
