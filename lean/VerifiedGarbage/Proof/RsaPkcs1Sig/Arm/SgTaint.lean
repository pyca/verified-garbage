module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Sign
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Sign
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # RSASSA-PKCS1-v1_5 signing on ARMv7: the pieces the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Sg

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Sign

theorem cmp_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r3]) (.block [.cmp .r3 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret0_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block ret0) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem fin_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r0 (.reg .r3)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Sig.Arm.Sg
