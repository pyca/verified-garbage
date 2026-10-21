module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.P384.X86_64.JointTiming
import VerifiedGarbage.Proof.P384.X86_64.NafTableTiming
import VerifiedGarbage.Proof.P384.X86_64.JointLayout
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.P384.X86_64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubleIn
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import VerifiedGarbage.Proof.Framework.LitShare
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P384.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P384.X86_64.NafTableTiming
meta import VerifiedGarbage.Proof.P384.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.P384.X86_64.Joint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubleIn
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase

/-! Concrete timing checks and the doubler of P-384's baseline and ADX joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.P384.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p384v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTableCoZ_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p384vx publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,nafTableCoZ_adx_checks,nafCacheTable_adx_ct,
    joint_adx_infinity_ct,joint_adx_counter_ct,fastGenerator_adx_checks,fastPeer_adx_checks⟩

theorem joint_doubler (hc : CfgOk p384v) (hC : Weierstrass.Law p384v.C) :
    JointDoubler publicJoint p384v.C size (jointDouble publicJoint.K) :=
  doubleIn_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    (by decide) jointDouble_ct

theorem joint_adx_doubler (hc : CfgOk p384vx) (hC : Weierstrass.Law p384vx.C) :
    JointDoubler publicJointAdx p384vx.C size (jointDoubleAdx publicJointAdx.K) :=
  doubleCms_doubler joint_adx_add_layout (by decide +kernel) (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    (by decide) jointDouble_adx_ct

/-- `jointPrefix p384v` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix p384v)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p384v) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p384v).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384v).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384v).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `jointPrefix p384vx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixAdxErased : Prog isa := Code.erase (jointPrefix p384vx)

materialize_shared jointPrefixAdxErased

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p384vx) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixAdxErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p384vx).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailAdxErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384vx).inline

materialize_shared jointTailAdxErased

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p384vx).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailAdxErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P384
