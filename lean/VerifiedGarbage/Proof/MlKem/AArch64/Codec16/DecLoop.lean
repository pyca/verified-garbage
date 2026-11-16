module
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Eight-coefficient decoding loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (decMath maskVec)
open VG.Proof.Rc4.AArch64


theorem decMask_value : decMask = 0xff0b0a09ff080706ff050403ff020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte decMask e = vbyte 0xff0b0a09ff080706ff050403ff020100#128 e)

end VG.Proof.MlKem.AArch64.Codec16
