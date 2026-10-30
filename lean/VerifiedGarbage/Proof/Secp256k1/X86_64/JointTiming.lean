module

import VerifiedGarbage.Proof.Secp256k1.X86_64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Impl.Secp256k1.X86_64.PointOps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.JacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
meta import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.PointOps
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
meta import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase

/-! Taint checks of the rest of secp256k1's joint loop: its digits' reads and
entries, the cache of `Z²`, `Z³`, the seed, the counter, the recoders, the
doubler and the table by calls. -/

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

/-- The table by calls' copy of `Q` to `R`. -/
theorem tableCopyInit_ct : ScratchCT (.block (copyPt publicJoint.K.M.n publicJoint.K.R publicJoint.K.P)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The table by calls' copy of `Q` to its first entry. -/
theorem tableCopyFirst_ct :
    ScratchCT (.block (copyPt publicJoint.K.M.n (publicJoint.K.tblPt 1) publicJoint.K.P)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem tableCounter_ct : ScratchCT (.block [.mov32 .rbx (.imm 1)]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The store of `R` in the entry `rbx` selects. -/
theorem tableStore_ct : RegCT [.rdi,.rbx] (.block (Naf.tableStore publicJoint.K)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx]) (fun _ _ _ _ h => h) (by taint_decide)

theorem tableAdvance_ct : RegCT [.rbx] (.block [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 8)]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The table by calls' copy of `2Q` to `E`. -/
theorem tableE_ct : ScratchCT (.block (copyPt publicJoint.K.M.n publicJoint.K.E publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The table by calls' copy of `2Q` to its ninth entry. -/
theorem tableTwice_ct :
    ScratchCT (.block (copyPt publicJoint.K.M.n (Naf.twice publicJoint.K) publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- `E`'s `Z²` and `Z³`, for the table's cached additions. -/
theorem cacheE_ct : ScratchCT (fprogB publicJoint.K.M (Joint.cacheE publicJoint)).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- `vg_secp256k1_jac_add_cached` keeps the table's counter in `rbx`. -/
theorem addCachedFn_keeps : KeepReg.keeps .rbx Impl.Secp256k1.X86_64.PointOps.addCachedFn = true := by
  rw [← KeepReg.keepsN_eq]
  lit_decide

end VG.Proof.Secp256k1.X86_64
