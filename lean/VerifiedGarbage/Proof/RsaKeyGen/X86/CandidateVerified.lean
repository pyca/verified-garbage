module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateConstantTime
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSatisfiable

/-! # Native candidate generation has complete correctness, timing, and satisfiability certificates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem verified {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56) :
    Verified target (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) contract :=
  ⟨correct montVerified montNoSp montStack roundVerified roundNoSp roundStack,
    constantTime montVerified montNoSp montStack roundVerified roundNoSp roundStack, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Candidate
