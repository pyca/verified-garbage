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

 theorem entry_check : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4)
    (.block BatchCtr.entry) h).isSome = true := ⟨_, by taint_decide⟩

 theorem prepArgs_check : ∃ h, (taint.check (Taint.ofRegs [.r4, .r8])
    (.block [movR .r0 .r4, .mov .r1 (.imm 0), movR .r2 sb, .mov .r3 (.imm 182)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

 theorem setup_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r7, .r8])
    (.block (BatchCtr.copyCounterIn ++ ([.cmp .r7 (.imm 0)] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

 theorem count_check : ∃ h, (taint.check (Taint.ofRegs [.r7]) BatchCtr.count h).isSome = true :=
  ⟨_, by taint_decide⟩

 theorem fill_check : ∃ h, (taint.check (Taint.ofRegs [.r8, .r11]) BatchCtr.fill h).isSome = true :=
  ⟨_, by taint_decide⟩

 theorem cryptArgs_check : ∃ h, (taint.check (Taint.ofRegs [.r8])
    (.block [movR .r0 sb, .mov .r1 (.imm 182)]) h).isSome = true := ⟨_, by taint_decide⟩

 theorem xor_check : ∃ h, (taint.check (Taint.ofRegs [.r6, .r8, .r11]) BatchCtr.xorGroup h).isSome = true :=
  ⟨_, by taint_decide⟩

 theorem advance_check : ∃ h, (taint.check (Taint.ofRegs [.r7, .r11])
    (.block [.subs .r7 .r7 (.reg .r11)]) h).isSome = true := ⟨_, by taint_decide⟩

 theorem finish_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r8]) BatchCtr.finish h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem prepare_check : ∃ h, (taint.check (Taint.ofRegs [.r4, .r8]) BatchCtr.prepare h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem crypt_check : ∃ h, (taint.check (Taint.ofRegs [.r8]) BatchCtr.crypt h).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.BatchTaint
