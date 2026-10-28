module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory

/-! # Trial division: the status 3 written, or `eax = 4` to go on -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def SieveOutputs (E : Environment) (e : Nat) (entropy : List Byte) (s : State) : Prop :=
  if Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy) then
    Outputs E 3 E.length (List.replicate E.length 0) s
  else ExponentOutputs E e entropy s

end VG.Proof.RsaKeyGen.X86.Candidate
