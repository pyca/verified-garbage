module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialOfb
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Sm4.Arm.SerialOfb
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-! # Constant-time input filling and encryption for OFB -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialOfbTaint
open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8])
    (.seq SerialCfb.count (.seq BatchCfb.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

theorem groupTail_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8, .r11])
    (.seq BatchCtr.xorGroup (.seq (.block SerialOfb.saveFeedback)
      (.block [.subs .r7 .r7 (.reg .r11)]))) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.SerialOfbTaint
