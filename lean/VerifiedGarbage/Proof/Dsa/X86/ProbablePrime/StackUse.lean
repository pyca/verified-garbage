module

public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStackUse
public import VerifiedGarbage.Spec.Dsa

/-! # The probable-prime test uses at most 152 bytes below its caller -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Impl.Dsa.X86.ProbablePrime

theorem test_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (test bits montName mont roundName round) ≤ 136 := by
  have bound := VG.Proof.RsaKeyGen.X86.CandidateStackUse.testWith Hm Hr (bits - 1) (Spec.Dsa.primeChecks bits)
    (8 * ((bits + 63) / 64)) (bits / 32) (width bits) montName roundName
  change max (stackUse (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith (bits - 1) (Spec.Dsa.primeChecks bits)
    (8 * ((bits + 63) / 64)) (bits / 32) (width bits) montName mont roundName round)) (stackUse finish) ≤ 136
  have : stackUse finish = 0 := rfl
  omega

theorem sieved_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (sieved bits montName mont roundName round) ≤ 136 := by
  have bound := test_stack Hm Hr bits montName roundName
  have sieve : stackUse (VG.Impl.RsaKeyGen.X86.CandidateSieve.code (width bits)) = 24 := rfl
  have used : stackUse (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 2) = 0 := rfl
  change max (stackUse (VG.Impl.RsaKeyGen.X86.CandidateSieve.code (width bits)))
    (max 0 (max (stackUse (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 2))
      (stackUse (test bits montName mont roundName round)))) ≤ 136
  omega

theorem body_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (body bits montName mont roundName round) ≤ 136 := by
  have bound := sieved_stack Hm Hr bits montName roundName
  have loaded : stackUse (load (bits / 32) (width bits)) = 0 := rfl
  change max 0 (max (stackUse (load (bits / 32) (width bits))) (stackUse (sieved bits montName mont roundName round))) ≤ 136
  omega

theorem code_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (code bits montName mont roundName round) ≤ 152 := by
  have bound := body_stack Hm Hr bits montName roundName
  change max (stackUse (body bits montName mont roundName round)) 0 + 16 ≤ 152
  omega

end VG.Proof.Dsa.X86.ProbablePrime
