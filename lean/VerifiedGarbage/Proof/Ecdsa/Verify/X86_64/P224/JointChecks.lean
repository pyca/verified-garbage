module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.P224.X86_64.NafTableTiming
import VerifiedGarbage.Proof.P224.X86_64.JointLayout
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.P224.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P224.X86_64.NafTableTiming
meta import VerifiedGarbage.Proof.P224.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.P224.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.P224.X86_64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
meta import VerifiedGarbage.Proof.P224.X86_64.JacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64

/-! ### `P224.X86_64.JointTiming`, which only this module used -/

section

/-! Taint checks of the rest of P-224's joint loop: its digits' reads and
entries, the cache of `Z²`, `Z³`, the seed, the counter, the recoders and the
doubler. -/

@[expose] public section

namespace VG.Proof.P224.X86_64
open VG VG.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Proof.Weierstrass.X86_64

theorem joint_cached_checks : JointCachedChecks publicJoint := by
  refine ⟨?_,?_,nafCachedJac_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_fixed_checks : JointFixedChecks publicJoint := by
  refine ⟨?_,?_,nafMixedJac_checks,joint_cached_checks.copy⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taintSym ["VG_P224_COMB"]) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_ct : ScratchCT (Joint.cacheCode publicJoint).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJoint.K publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top publicJoint)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_checks : FastPrepChecks 4 (p224v.sl V) p224v.winBits 5 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastGenerator_checks : FastPrepChecks 4 (p224v.sl U) 6000 7 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem jointDouble_ct : ScratchCT (fprogB publicJoint.K.M (dblJMul publicJoint.K.S publicJoint.K.R publicJoint.K.D)).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P224.X86_64

end

end

/-! Concrete timing checks and the doubler of P-224's joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.P224.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p224v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTable_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator_checks,fastPeer_checks⟩

theorem joint_doubler (hc : CfgOk p224v) (hC : Weierstrass.Law p224v.C) :
    JointDoubler publicJoint p224v.C size (Joint.jacDouble publicJoint.K) :=
  jacDouble_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    jointDouble_ct joint_cached_checks.copy

/-- `jointPrefix p224v` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix p224v)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p224v) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p224v).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p224v).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p224v).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P224
