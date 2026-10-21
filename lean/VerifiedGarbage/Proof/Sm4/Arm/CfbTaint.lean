module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-! # Constant-time input filling and encryption for CFB decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CfbTaint
open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8])
    (.seq BatchCtr.count (.seq BatchCfb.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.CfbTaint
