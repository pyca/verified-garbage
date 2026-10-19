module

public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Impl.Rsa.Arm.CheckKey
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.CheckKey
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_check_key` on ARMv7: the pieces that read the stack arguments

The entry (from the arguments in `r0`–`r3` and on the stack) and the
restore of the registers, checked by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckKey
open VG VG.Arm VG.Impl.Rsa.Arm.KeyCheck

theorem entry_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] (4 * 14))
    (entry (4 * 12) ([(0, aD), (2, aP), (4, aQ), (6, aDP), (8, aDQ), (10, aQI)].map
      fun p => (4 * p.1, p.2))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] (4 * 14)) (.block (restore (4 * 12))) hc).isSome =
    true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.CheckKey
