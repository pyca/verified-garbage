module

public import VerifiedGarbage.Impl.Rsa.Arm.CheckCrtKey
meta import VerifiedGarbage.Impl.Rsa.Arm.CheckCrtKey
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_check_crt_key` on ARMv7: the pieces that read the stack arguments

The entry (from the arguments in `r0`–`r3` and on the stack) and the
restore of the registers, checked by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Impl.Rsa.Arm.KeyCheck

theorem entry_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] (4 * 12))
    (entry (4 * 10) ([(0, aP), (2, aQ), (4, aDP), (6, aDQ), (8, aQI)].map fun p => (4 * p.1, p.2))) hc).isSome =
      true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] (4 * 12)) (.block (restore (4 * 10))) hc).isSome =
    true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.CheckCrtKey
