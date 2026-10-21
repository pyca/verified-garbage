module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
import VerifiedGarbage.Proof.P384.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9Timing
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9Timing
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! Concrete timing certificates for the joint P-384 verifier. -/
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64

theorem prep9_checks : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U) where
  init := by reg_ct [.x0]
  step := by reg_ct (PubNaf.prepPublic P384Joint.KG.M.n)

theorem prep5_checks : PubNaf.PrepChecks P384Joint.K (p384.sl V) :=
  P384.prep_checks

theorem window_checks : PubNaf.WindowChecks P384Joint.K := P384.window_checks

theorem double_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    P384Joint.double :=
  P384.EcdhDouble.Certificate.ctRD

theorem before_ct : ConstantTime isa (fun _=>True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p384) :=
  LaneTaint.constantTime (Taint.ofRegs [.x0,.x1,.x2,.x3]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem tail_ct : FieldCT (VG.Impl.Ecdsa.Verify.AArch64.Cfg.tail p384) := by reg_ct [.x0]
theorem mixed_checks : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D where
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
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
