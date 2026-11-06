module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-! # Taint checks for the code between SM4-CTR's prepared-helper calls

These checks cover the pure instruction phases. Calls are composed separately
using their verified contracts; these checks alone do not establish constant
time for the complete CTR implementation.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchTaint

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)

 theorem setup_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r7, .r8])
    (.block (BatchCtr.copyCounterIn ++ ([.cmp .r7 (.imm 0)] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

 theorem finish_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r8]) BatchCtr.finish h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r7, .r8])
    (.seq BatchCtr.count (.seq BatchCtr.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

theorem groupTail_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8, .r11])
    (.seq BatchCtr.xorGroup (.block [.subs .r7 .r7 (.reg .r11)])) h).isSome = true := ⟨_, by taint_decide⟩

theorem proHead_check : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4)
    (.seq (.block BatchCtr.entry) BatchCtr.prepare) h).isSome = true := ⟨_, by taint_decide⟩

theorem nil_check : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.BatchTaint
