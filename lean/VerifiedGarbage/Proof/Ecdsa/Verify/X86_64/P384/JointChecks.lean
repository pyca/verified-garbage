module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointContract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointContract
public import VerifiedGarbage.Proof.P384.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P384.X86_64.JointTiming
public import VerifiedGarbage.Proof.P384.X86_64.NafTableTiming
meta import VerifiedGarbage.Proof.P384.X86_64.NafTableTiming
public import VerifiedGarbage.Proof.P384.X86_64.JointLayout
meta import VerifiedGarbage.Proof.P384.X86_64.JointLayout
public import VerifiedGarbage.Proof.P384.X86_64.JointFrame
meta import VerifiedGarbage.Proof.P384.X86_64.JointFrame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
meta import VerifiedGarbage.Spec.EcKey.Generic

/-! Concrete timing checks and the doubler of P-384's baseline and ADX joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.P384.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p384v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTable_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p384vx publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,nafTable_adx_checks,nafCacheTable_adx_ct,
    joint_adx_infinity_ct,joint_adx_counter_ct,fastGenerator_adx_checks,fastPeer_adx_checks⟩

theorem joint_doubler (hc : CfgOk p384v) (hC : Weierstrass.Law p384v.C) :
    JointDoubler publicJoint p384v.C size (Joint.jacDouble publicJoint.K) :=
  jacDouble_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    jointDouble_ct joint_cached_checks.copy

theorem joint_adx_doubler (hc : CfgOk p384vx) (hC : Weierstrass.Law p384vx.C) :
    JointDoubler publicJointAdx p384vx.C size (Joint.jacDouble publicJointAdx.K) :=
  jacDouble_doubler joint_adx_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    jointDouble_adx_ct joint_adx_cached_checks.copy

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p384v) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p384vx) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384v).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384vx).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P384
