module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Safety
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Recognize

/-! Recognition uses baseline integer instructions without writing the stack pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

theorem sp_safe (v : RoundImpl) : (emittedCode v).all (fun i => !isa.writesSp i) = true := by
  have safePrefix : (recognizeCode.all (fun i => !isa.writesSp i)) = true := by
    apply Code.all_of_allInstrs
    decide +kernel
  have restoreSafe : (Code.block restore : Prog isa).all (fun i => !isa.writesSp i) = true := by
    apply Code.all_of_allInstrs
    decide +kernel
  change (recognizeCode.all (fun i => !isa.writesSp i) &&
    (true && (true && ((Code.block restore : Prog isa).all (fun i => !isa.writesSp i) &&
      (CheckDomain.domainCode v).all (fun i => !isa.writesSp i))))) = true
  rw [safePrefix, restoreSafe, CheckDomain.domainCode_sp v]
  rfl

end VG.Proof.Ffdh.X86_64.VettedValidation
