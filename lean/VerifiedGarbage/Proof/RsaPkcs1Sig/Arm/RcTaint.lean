module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the pieces the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm

theorem fin_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r0 (.reg .r3)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Sig.Arm.Rc
