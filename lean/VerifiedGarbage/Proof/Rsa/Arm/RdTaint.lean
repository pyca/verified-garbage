module

public import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_recover_primes_det` on ARMv7: the pieces the taint analysis checks

Between the division, `inverse` and the loops, each piece computes its
addresses and counts from `r7`–`r9` (`ctxRegs`), and switches between the
narrow and wide arrays from `r9` alone; the loads of `w` from the header
after a division need only `r8`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.RecoverDet
open VG.Proof.Rsa.Arm.Recover (ctxRegs)

/-- A piece the taint analysis checks with `r7`–`r9` public. -/
abbrev DCert (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check taint (Taint.ofRegs ctxRegs) c hc).isSome = true

theorem deMinus_taint : DCert deMinus := ⟨_, by taint_decide⟩
theorem twosPre_taint : DCert twosPre := ⟨_, by taint_decide⟩
theorem twosBody_taint : DCert twosBody := ⟨_, by taint_decide⟩
theorem gcdCopy_taint : DCert (copy aGx aX2) := ⟨_, by taint_decide⟩
theorem gcdPost_taint : DCert gcdPost := ⟨_, by taint_decide⟩
theorem productPreA_taint : DCert (productPre wA wZ) := ⟨_, by taint_decide⟩
theorem productStepA_taint : DCert (productStep aG wX3 wA wT1 wT2 wZ) := ⟨_, by taint_decide⟩
theorem productStepB_taint : DCert (productStep aBy wB wA wT1 wT2 wZ) := ⟨_, by taint_decide⟩
theorem divAPre_taint : DCert divAPre := ⟨_, by taint_decide⟩
theorem divAPost_taint : DCert divAPost := ⟨_, by taint_decide⟩
theorem divBPre_taint : DCert divBPre := ⟨_, by taint_decide⟩
theorem eqExact_taint : DCert (eqS sExact aRem aZN VG.Impl.Rsa.Arm.Recover.aW) := ⟨_, by taint_decide⟩
theorem squarePre_taint : DCert squarePre := ⟨_, by taint_decide⟩
theorem minus4n_taint : DCert minus4n := ⟨_, by taint_decide⟩
theorem sqrtPre_taint : DCert sqrtPre := ⟨_, by taint_decide⟩
theorem sqrtBody_taint : DCert sqrtBody := ⟨_, by taint_decide⟩
theorem eqOk5_taint : DCert (eqS sOk5 aRm aZN VG.Impl.Rsa.Arm.Recover.aW) := ⟨_, by taint_decide⟩
theorem factors_taint : DCert factors := ⟨_, by taint_decide⟩

theorem restoreW_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block restoreW) hc).isSome = true := ⟨_, by taint_decide⟩
theorem ctxw_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block VG.Impl.Rsa.Arm.Recover.ctxw) hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.RecoverDet
