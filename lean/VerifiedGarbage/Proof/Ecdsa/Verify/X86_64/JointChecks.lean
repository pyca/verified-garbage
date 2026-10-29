module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.P256.X86_64.JointLoop
import VerifiedGarbage.Proof.P256.X86_64.JointTiming
import VerifiedGarbage.Proof.P256.X86_64.JointWindowTiming
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublicTiming
import VerifiedGarbage.Proof.P256.X86_64.NafTableTiming
import VerifiedGarbage.Proof.P256.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.P256.X86_64.Joint
import VerifiedGarbage.Proof.P256.X86_64.NafCacheTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JointLoop
meta import VerifiedGarbage.Proof.P256.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P256.X86_64.JointWindowTiming
meta import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublicTiming
meta import VerifiedGarbage.Proof.P256.X86_64.NafTableTiming
meta import VerifiedGarbage.Proof.P256.X86_64.FastNafTiming
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.P256.X86_64.Joint
meta import VerifiedGarbage.Proof.P256.X86_64.NafCacheTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
meta import VerifiedGarbage.Proof.P256.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Concrete timing checks for baseline and ADX public joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.P256.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p256v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTableCoZ_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator16_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p256vx publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,nafTableCoZ_adx_checks,
    nafCacheTable_adx_ct,joint_adx_infinity_ct,joint_adx_counter_ct,fastGenerator16_adx_checks,
    fastPeer_adx_checks⟩

theorem joint_doubler (hc : CfgOk p256v) (hC : Weierstrass.Law p256.C) :
    JointDoubler publicJoint p256.C size (jointDouble publicJoint.K) :=
  p256_doubler joint_layout rfl (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3 joint_double_nodup
    doubleHalfPublic_ct

theorem joint_adx_doubler (hc : CfgOk p256vx) (hC : Weierstrass.Law p256vx.C) :
    JointDoubler publicJointAdx p256vx.C size (jointDouble publicJointAdx.K) :=
  p256_doubler joint_adx_layout rfl (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3 joint_adx_double_nodup
    doubleHalfPublic_adx_ct

/-- `jointPrefix p256v` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix p256v)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p256v) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `jointPrefix p256vx` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixAdxErased : Prog isa := Code.erase (jointPrefix p256vx)

materialize_shared jointPrefixAdxErased

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p256vx) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixAdxErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p256v).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256v).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256v).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p256vx).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailAdxErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256vx).inline

materialize_shared jointTailAdxErased

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256vx).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailAdxErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64
