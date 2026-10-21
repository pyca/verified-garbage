module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTestsMath

/-! Screening stages of the existing candidate specification, before witness tests. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def candidateRejected (p : CandidateParams) : Option (Bool × List Byte) :=
  some (false, p.bytes.drop p.length)

def candidateScreenQ (p : CandidateParams) : Option (Bool × List Byte) :=
  if (Spec.Ffdh.primeShape ((p.candidate - 1) / 2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) then candidateTests p p.length else candidateRejected p

def candidateScreenP (p : CandidateParams) : Option (Bool × List Byte) :=
  if (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) then candidateScreenQ p else candidateRejected p

def candidateScreen (p : CandidateParams) : Option (Bool × List Byte) :=
  if Spec.Ffdh.generationShape p.bits p.generator p.candidate then candidateScreenP p else candidateRejected p

end VG.Proof.Ffdh.Arm.ParameterCandidate
