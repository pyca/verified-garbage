module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def candidateShapes (p : CandidateParams) : Bool :=
  (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) &&
    (Spec.Ffdh.primeShape ((p.candidate-1)/2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate-1)/2))

theorem candidateScreenP_shapes (p : CandidateParams) :
    candidateScreenP p = if candidateShapes p then candidateTests p p.length else candidateRejected p := by
  unfold candidateScreenP candidateScreenQ candidateShapes
  cases (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) <;>
    cases (Spec.Ffdh.primeShape ((p.candidate-1)/2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate-1)/2)) <;> rfl

theorem candidateScreenP_even (p : CandidateParams) (even : ((p.candidate-1)/2)%2=0) :
    candidateScreenP p=candidateRejected p := by
  rw [candidateScreenP_shapes]
  simp only [candidateShapes,even_primeShape even,Bool.false_and,Bool.and_false,Bool.false_eq_true,ite_false]

end VG.Proof.Ffdh.Arm.ParameterCandidate
