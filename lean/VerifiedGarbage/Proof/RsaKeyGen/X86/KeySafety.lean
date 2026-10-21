module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpCode
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
public import Init.Prelude
public import VerifiedGarbage.TCB.X86.Isa

/-! # Registration checks the complete native key routine's stack-pointer discipline -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem code_sp : (VG.Impl.RsaKeyGen.X86.Key.code).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal]
  exact KeyNoSp.checked KeyNoSp.code_noSp

end VG.Proof.RsaKeyGen.X86.Key
