module

import VerifiedGarbage.Proof.Secp256k1.X86_64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Impl.Secp256k1.X86_64.PointOps
import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.JacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.PointOps
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit

/-! Taint checks of the rest of secp256k1's joint loop: its digits' reads and
entries, the cache of `Z²`, `Z³`, the seed, the counter, the recoders and the
doubler. -/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64
open VG VG.X86_64 VG.Impl.Secp256k1.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
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
  · exact VG.Taint.constantTime (A:=taintSym ["VG_SECP256K1_GTAB"]) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_ct : ScratchCT (Joint.cacheCode publicJoint).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJoint.K publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top publicJoint)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_checks : FastPrepChecks 4 (secp256k1v.sl V) secp256k1v.winBits 5 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastGenerator16_checks : FastPrepChecks16 4 (secp256k1v.sl U) 6000 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 4))
      (fun _ _ _ _ h => h) (by taint_decide)

/-- The doubling of `vg_secp256k1_jac_double`'s body, into `D`. -/
theorem jointDouble_ct :
    ScratchCT (fprogB publicJoint.K.M (dblJ0 publicJoint.K.S publicJoint.K.R publicJoint.K.D)).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- `vg_secp256k1_jac_double`: its timing depends only on `rdi`, a straight
line of field operations at `rdi` plus constants (checked on its literal). -/
theorem doubleFn_ct : ScratchCT Impl.Secp256k1.X86_64.PointOps.doubleFn :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Secp256k1.X86_64
