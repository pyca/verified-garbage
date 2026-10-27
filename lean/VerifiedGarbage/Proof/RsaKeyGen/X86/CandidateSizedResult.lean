module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCloseInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory

/-! # A supported candidate width draws the candidate and filters it by distance and trial division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def FilteredOutputs (E : Environment) (e : Nat) (p : Option Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.tooClose (8 * E.length) p (candidateValue E entropy) then
    Outputs E 2 E.length (List.replicate E.length 0) s
  else SieveOutputs E e entropy s

/-- After the code for the width: the status 2 or 3 written, or `eax = 4`
and the drawn candidate to go on. -/
def FrontOutputs (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy) then
    Outputs E 2 E.length (List.replicate E.length 0) s
  else if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else Drawn E eBytes pBytes entropy s ∧ s.gpr .eax = 4

end VG.Proof.RsaKeyGen.X86.Candidate
