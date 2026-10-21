module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The shared native key implementation preserves ESP between its ABI frame operations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86

theorem body_noSp : NoSp VG.Impl.RsaKeyGen.X86.KeyRuntime.body := NoSp.of_all (by rfl)

theorem code_sp : (VG.Impl.RsaKeyGen.X86.KeyRuntime.code).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal]
  exact VG.Proof.RsaKeyGen.X86.KeyNoSp.checked (NoSp.of_all (by rfl))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
