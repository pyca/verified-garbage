module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-! # Constant-time checks around CBC's prepared cipher phase -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcTaint
open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6, .r7, .r8])
    (.seq BatchCtr.count (.seq BatchCbc.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

theorem groupTail_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6, .r7, .r8, .r11])
    (.seq (BatchCbc.chooseXor 0 8) (.seq (.block BatchCtr.copyCounterIn) (.block BatchCbc.advance))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem proHead_check : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4)
    (.seq (.block BatchCtr.entry) BatchCbc.prepare) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.CbcTaint
