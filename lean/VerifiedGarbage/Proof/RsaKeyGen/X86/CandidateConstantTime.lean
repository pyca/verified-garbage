module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrameTiming

/-! # Native candidate generation is constant time under exactly the shared contract's declared leak -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem constantTime {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) :
    ConstantTime isa contract.pre contract.pub (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  have P := public_inputs HP
  have I := entry_input HS
  have J := entry_input HT
  rw [← P.environment, ← P.exponent] at J
  exact framed_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (call_valid HS) P.leak _ _ _ _ _ _ ⟨⟨I, J⟩, P.stack⟩ A B

end VG.Proof.RsaKeyGen.X86.Candidate
