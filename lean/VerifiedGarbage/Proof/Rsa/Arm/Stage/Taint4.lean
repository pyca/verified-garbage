module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The ARMv7 key stages: the pieces of the factors the taint analysis checks -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

theorem storeP_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
    (VG.Impl.Rsa.Arm.CrtValues.store 5) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem storeQ_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
    (VG.Impl.Rsa.Arm.CrtValues.store 6) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block [.ldr .r0 .r8 sMask]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.Recover
