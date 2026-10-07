import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import VerifiedGarbage.Proof.P384.X86_64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-! Baseline and ADX taint checks of the rest of P-384's joint loop: its digits'
reads and entries, the cache of `Z²`, `Z³`, the seed, the counter, the
recoders and the doubler. -/
namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Proof.Weierstrass.X86_64

theorem joint_cached_checks : JointCachedChecks publicJoint := by
  refine ⟨?_,?_,nafCachedJac_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_cached_checks : JointCachedChecks publicJointAdx := by
  refine ⟨?_,?_,nafCachedJac_adx_checks,?_⟩
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
  · exact VG.Taint.constantTime (A:=taintSym ["VG_P384_COMB"]) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_fixed_checks : JointFixedChecks publicJointAdx := by
  refine ⟨?_,?_,nafMixedJac_adx_checks,joint_adx_cached_checks.copy⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taintSym ["VG_P384_COMB"]) (Taint.ofRegs [.rdi,.r8])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_ct : ScratchCT (Naf.cacheTable publicJoint.K.M publicJoint.K.tbl publicJoint.cache 8) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_adx_ct :
    ScratchCT (Naf.cacheTable publicJointAdx.K.M publicJointAdx.K.tbl publicJointAdx.cache 8) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJoint.K publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJointAdx.K publicJointAdx.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (64*publicJoint.K.M.n)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_counter_ct :
    ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (64*publicJointAdx.K.M.n)))]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_checks : FastPrepChecks 6 (p384v.sl V) p384v.winBits 5 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 6))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastGenerator_checks : FastPrepChecks 6 (p384v.sl U) 6400 7 := by
  constructor
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs (nafPrepPublicN 6))
      (fun _ _ _ _ h => h) (by taint_decide)

theorem fastPeer_adx_checks : FastPrepChecks 6 (p384vx.sl V) p384vx.winBits 5 := fastPeer_checks

theorem fastGenerator_adx_checks : FastPrepChecks 6 (p384vx.sl U) 6400 7 := fastGenerator_checks

theorem jointDouble_ct : ScratchCT (fprogB publicJoint.K.M (dblJMul publicJoint.K.S publicJoint.K.R publicJoint.K.D)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem jointDouble_adx_ct :
    ScratchCT (fprogB publicJointAdx.K.M (dblJMul publicJointAdx.K.S publicJointAdx.K.R publicJointAdx.K.D)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P384.X86_64
