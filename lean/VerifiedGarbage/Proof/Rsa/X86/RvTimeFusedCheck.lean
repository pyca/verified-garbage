module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedMultiply
public import VerifiedGarbage.Proof.Rsa.X86.RvTaint
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.RvFusedSmall
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedSmall
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass

/-! Taint checks for the call-free pieces of fused recovery. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.RecoverRt
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.Keys

/-- Grouping the pure work between a square and candidate multiplication. -/
def fusedBefore : Prog isa := .seq (.seq (.seq (eqAt sE1 mX aO)
  (eqAt sE2 mX aNg)) fusedHit) (VG.Impl.Rsa.X86.KeyRt.sel nar 0 0 mY sLive)

def fusedAfter : Prog isa := seqs [VG.Impl.Rsa.X86.KeyRt.sel nar mY mX mXm sBit,
  eqAt sE1 mY aO, eqAt sE2 mY aNg, fusedTail]

theorem fusedSmallStartCheck : (VG.Taint.check sseTaint τA (fusedSmallStart)
    (VG.Taint.hintOf sseTaint τA (fusedSmallStart))).isSome = true := by
  taint_decide

theorem fusedSmallStepCheck : ∃ hint, (VG.Taint.check sseTaint τA (fusedSmallStep)
    hint).isSome = true := ⟨_, by taint_decide⟩

theorem fusedSmall7Check : ∃ hint, (VG.Taint.check sseTaint τA (fusedSmall7)
    hint).isSome = true := ⟨_, by taint_decide⟩

theorem fusedBeforeCheck : (VG.Taint.check sseTaint τA (fusedBefore)
    (VG.Taint.hintOf sseTaint τA (fusedBefore))).isSome = true := by
  taint_decide

theorem fusedAfterCheck : ∃ hint, (VG.Taint.check sseTaint τA (fusedAfter)
    hint).isSome = true := ⟨_, by taint_decide⟩

theorem fusedInitCheck : (VG.Taint.check sseTaint τA (fusedInit)
    (VG.Taint.hintOf sseTaint τA (fusedInit))).isSome = true := by
  taint_decide

theorem fusedFinishCheck : (VG.Taint.check sseTaint τA (fusedFinish)
    (VG.Taint.hintOf sseTaint τA (fusedFinish))).isSome = true := by
  taint_decide

theorem fusedPrepareCheck : (VG.Taint.check sseTaint τA (fusedPrepare)
    (VG.Taint.hintOf sseTaint τA (fusedPrepare))).isSome = true := by
  taint_decide

theorem fusedWindowTopCheck : (VG.Taint.check sseTaint τA (.block windowTop)
    (VG.Taint.hintOf sseTaint τA (.block windowTop))).isSome = true := by
  taint_decide

theorem fusedShiftUpCheck : (VG.Taint.check sseTaint τA (shiftUp)
    (VG.Taint.hintOf sseTaint τA (shiftUp))).isSome = true := by
  taint_decide

theorem fusedBitHeadCheck (k : Nat) (hk : k ≤ 3) :
    (VG.Taint.check sseTaint τA (.block (fusedBitHead k))
      (VG.Taint.hintOf sseTaint τA (.block (fusedBitHead k)))).isSome = true := by
  match k, hk with
  | 0, _ => first | rfl | taint_decide
  | 1, _ => first | rfl | taint_decide
  | 2, _ => first | rfl | taint_decide
  | 3, _ => first | rfl | taint_decide

end VG.Proof.Rsa.X86.Recover
