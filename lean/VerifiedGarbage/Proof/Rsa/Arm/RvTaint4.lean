module

public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the pieces of the factors the taint analysis checks -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

theorem ym1_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sub3 0 mY aOne) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem oneN_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy 1 aN) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mN_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aM aN) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem twoZ_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy 2 aZ) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem setOne2_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block (setOne 2)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem threeZ_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy 3 aZ) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zeroZ'_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aZero aZ) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nm_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sub3 aNM aZero aM) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem qN_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aQ aN) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dvP_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (copy aDv 1) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divHdr_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs)
    (.block (clrW aDv ++ VG.Impl.Rsa.Arm.CrtValues.divHdr aQ aRm aDv aDt)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem lt_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sub3 aW 1 aQ) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ltStore_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs)
    (.block [.str .r11 .r8 sLt]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem selP_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sel 5 1 aQ sLt) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem selQ_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (sel 6 aQ 1 sLt) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem storeP_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
    (VG.Impl.Rsa.Arm.CrtValues.store 5) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem storeQ_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
    (VG.Impl.Rsa.Arm.CrtValues.store 6) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ret_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) (.block [.ldr .r0 .r8 sMask]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.Recover
