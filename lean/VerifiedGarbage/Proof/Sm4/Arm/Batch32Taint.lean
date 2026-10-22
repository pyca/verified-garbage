module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
meta import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.TCB.Arm.Target

/-!
# Taint check for the group head of SM4's counter mode with `inc₃₂`

The one phase whose code differs from `BatchCtr`'s (`BatchTaint.lean`):
choosing the lanes, filling them (stepping the counter by `inc₃₂`) and the
call that encrypts them.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Taint

open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r7, .r8])
    (.seq BatchCtr.count (.seq BatchCtr32.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.Batch32Taint
