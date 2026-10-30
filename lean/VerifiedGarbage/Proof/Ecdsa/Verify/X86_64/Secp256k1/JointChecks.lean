module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointTiming
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointLayout
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointTable
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Proof.Weierstrass.JacDbl0
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.Secp256k1Literals
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.JointTiming
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.JointTable
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Secp256k1Literals
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Concrete timing checks and the doubler of secp256k1's joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Secp256k1.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Secp256k1.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks secp256k1v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,table_call_ct,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator16_checks,fastPeer_checks⟩

/-- secp256k1's `a` is `0`. -/
theorem secp256k1_a0 : Weierstrass.A0 Spec.Secp256k1.curve := rfl

theorem joint_doubler (hc : BaseCfgOk secp256k1v) (hC : Weierstrass.Law secp256k1v.C) :
    JointDoubler publicJoint secp256k1v.C size (jointDouble publicJoint.K) :=
  call_doubler (doubleBody_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _)
    (Weierstrass.jdblOk_dblJ0 hC secp256k1_a0) jointDouble_ct joint_cached_checks.copy) (by decide +kernel)
    (by decide) _

/-- `jointPrefix secp256k1v` without its displacements, as a literal of shared
blocks (`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix secp256k1v)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix secp256k1v) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail secp256k1v).inline` without its displacements, as a literal of
shared blocks (`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail secp256k1v).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail secp256k1v).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
