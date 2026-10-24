module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! Concrete timing certificates for the joint P-521 verifier. -/
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64

theorem prep7_checks : PubNafWide.PrepChecks P521Joint.KG (p521.sl U) where
  init := by reg_ct [.x0]
  step := by reg_ct (PubNaf.prepPublic P521Joint.KG.M.n)

theorem prep5_checks : PubNaf.PrepChecks P521Joint.K (p521.sl V) :=
  P521.prep_checks

theorem before_ct : ConstantTime isa (fun _=>True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p521) :=
  VG.Taint.constantTime_of_exists (A := VectorTaint.taint) (Taint.ofRegs [.x0, .x1, .x2, .x3], RegSet.empty)
    (fun _ _ _ _ h => VectorTaint.agree_initial h)
    (by taint_decide_sum [P521.mulPSum, P521.mulNSum, P521.sqrPSum, P521.validateSum, P521.scalarsSum,
      P521.nPowSum, P521.uvSum])

theorem tail_ct : FieldCT (VG.Impl.Ecdsa.Verify.AArch64.Cfg.tail p521) := by reg_ct [.x0]
theorem mixed_checks : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D where
  zero := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> reg_ct [.x0]
  copyQ := by reg_ct [.x0]
  init := by reg_ct [.x0]
  head := by reg_ct [.x0]
  tail := by reg_ct [.x0]
  double := by reg_ct [.x0]
  infinity := by reg_ct [.x0]
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
