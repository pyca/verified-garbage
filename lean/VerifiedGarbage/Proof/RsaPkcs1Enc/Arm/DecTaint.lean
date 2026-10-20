module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Decrypt
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Decrypt
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # RSAES-PKCS1-v1_5 decryption on ARMv7: the pieces the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt

theorem msgCL_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r3]) (.block (msgBytes lengthLabel clLen))
      hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem msgAM_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r3]) (.block (msgBytes messageLabel amLen))
      hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp12_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1, .r2]) (.block [.cmp .r1 (.reg .r2)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem maskBody_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1]) (.block maskBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem alBody_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r4, .r5, .lr]) (.block alBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem scanBody_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr]) (.block scanBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem validBlock_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block validBlock) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlStore_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block mlStore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem selBody_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr]) (.block selBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.RsaPkcs1Enc.Arm.Dec
