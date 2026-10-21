module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # Constant-time CBC input formation, encryption and feedback -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcTaint
open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8])
    (.seq SerialCbc.count SerialCbc.core) h).isSome = true := ⟨_, by taint_decide⟩

theorem groupTail_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8, .r11])
    SerialCbc.tail h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.SerialCbcTaint
