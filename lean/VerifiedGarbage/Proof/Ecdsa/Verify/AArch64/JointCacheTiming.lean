module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! ## `JointBoundaryChecks` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointTail_ct : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256) := by
  jac_field_ct

theorem jointFinish_ct : FieldCT (Jacobian.jacFinish cfg.K) := by
  jac_field_ct

theorem jointInit_ct : FieldCT (.block (Jacobian.infinity cfg.K cfg.K.R ++ ([.movz .x .x19 256 0] : List Instr))) := by
  jac_field_ct

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointCacheTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.P256Joint Spec.Weierstrass

/-- The cached table and two public recodings, before initializing the accumulator. -/
def JointCachePair (C : Curve) (base T : Addr) (P Q : Point C) (u v : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E s t) ∧
  JointStable cfg C base Q u v s ∧ JointStable cfg C base Q u v t ∧
  JointGenerator cfg C base 8192 P T s ∧ JointGenerator cfg C base 8192 P T t

end VG.Proof.Ecdsa.Verify.AArch64

end
