module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpCode
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare

/-! # Registration checks the complete native candidate's stack-pointer discipline -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem code_sp {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round).allInstrs (fun i => !isa.writesSp i) = true := by
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal]
  exact CandidateNoSp.checked (CandidateNoSp.code Hm Hr montName roundName)

end VG.Proof.RsaKeyGen.X86.Candidate
