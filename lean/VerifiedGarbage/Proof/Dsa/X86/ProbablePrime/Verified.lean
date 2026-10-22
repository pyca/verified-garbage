module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Correct
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ConstantTime
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Satisfiable
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.NoSp
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare

/-! # DSA's probable-prime test on i686 is verified -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86

theorem verified {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56) (bits : Nat)
    (low : 64 ≤ bits := by decide) (high : bits ≤ 4096 := by decide) (whole : bits % 32 = 0 := by decide) :
    Verified target (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) (contract bits) :=
  ⟨correct montVerified montNoSp montStack roundVerified roundNoSp roundStack ⟨low, high, whole⟩,
    constantTime montVerified montNoSp montStack roundVerified roundNoSp roundStack ⟨low, high, whole⟩,
    satisfiable ⟨low, high, whole⟩⟩

theorem code_all {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (bits : Nat) (montName roundName : String) :
    (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round).all (fun i => !isa.writesSp i) = true := by
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  refine Code.all_of_allInstrs ?_
  rw [equal]
  exact VG.Proof.RsaKeyGen.X86.CandidateNoSp.checked (code_noSp Hm Hr bits montName roundName)

end VG.Proof.Dsa.X86.ProbablePrime
