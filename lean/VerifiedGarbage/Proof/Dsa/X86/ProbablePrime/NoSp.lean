module

public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords

/-! # The probable-prime test never writes ESP outside its frames -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Impl.Dsa.X86.ProbablePrime VG.Proof.RsaKeyGen.X86.CandidateNoSp

theorem load_noSp (k w : Nat) : NoSp (load k w) := by
  unfold load VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  exact sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl))
    (sequence (witnessZeros _ _) (NoSp.of_all (by rfl))))

theorem test_noSp {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (bits : Nat)
    (montName roundName : String) : NoSp (test bits montName mont roundName round) :=
  sequence (testWith Hm Hr _ _ _ _ _ montName roundName) (NoSp.of_all (by rfl))

theorem sieved_noSp {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (bits : Nat)
    (montName roundName : String) : NoSp (sieved bits montName mont roundName round) := by
  apply NoSp.of_all
  simp only [sieved, Code.allInstrs, checked (test_noSp Hm Hr bits montName roundName)]
  rfl

theorem body_noSp {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (bits : Nat)
    (montName roundName : String) : NoSp (body bits montName mont roundName round) :=
  sequence (NoSp.of_all (by rfl)) (sequence (load_noSp _ _) (sieved_noSp Hm Hr bits montName roundName))

theorem code_noSp {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (bits : Nat)
    (montName roundName : String) : NoSp (code bits montName mont roundName round) := by
  apply NoSp.of_all
  simp only [code, Code.allInstrs, checked (body_noSp Hm Hr bits montName roundName)]
  rfl

end VG.Proof.Dsa.X86.ProbablePrime
