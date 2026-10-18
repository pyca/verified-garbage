module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix

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
  LaneTaint.constantTime (Taint.ofRegs [.x0,.x1,.x2,.x3]) (fun _ _ _ _ h=>h) (by taint_decide)

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
