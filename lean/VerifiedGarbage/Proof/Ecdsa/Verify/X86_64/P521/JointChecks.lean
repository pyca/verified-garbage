module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.P521.X86_64.JointTiming
import VerifiedGarbage.Proof.P521.X86_64.JointLayout
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Impl.P521.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P521.X86_64.JointTiming
meta import VerifiedGarbage.Proof.P521.X86_64.JointLayout
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Impl.P521.X86_64.Joint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
public import VerifiedGarbage.Proof.P521.X86_64.JacTiming
public import VerifiedGarbage.Proof.Framework.TaintMap
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
import VerifiedGarbage.Proof.P521.X86_64.FieldTmpl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
meta import VerifiedGarbage.Proof.P521.X86_64.JacTiming
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
meta import VerifiedGarbage.Proof.P521.X86_64.FieldTmpl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.X86_64.MulPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit

/-! ### `P521.X86_64.NafTableTiming`, which only this module used -/

section

/-! Baseline and ADX taint checks for P-521's verifier's odd-multiple table.

The field arithmetic is checked without its displacements, as the
templates of its operations (`FieldTmpl`), each analysed once; so is the
addition that keeps `rbx` (`KeepReg.keepsN`, which the kernel evaluates
once for each template from the same state). -/

@[expose] public section

namespace VG.Proof.P521.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass.X86_64

theorem nafTable_checks : NafTableChecks nafJacWin := by
  have hT : p521T.Ok nafJacWin.M := p521HT_ok
  constructor
  · exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  iterate 3 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · constructor
    iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
    iterate 3 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
    exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · rw [← KeepReg.keeps_erase, ← KeepReg.keepsN_eq]
    simp only [Jacobian.jacAdd, Code.inline, Code.erase, Code.mapBlocks, hT.fprogB_mapBlocks]
    lit_decide
  · exact instrs_noClobber (by decide +kernel)

theorem nafTable_adx_checks : NafTableChecks nafJacWinAdx := by
  have hT : p521XT.Ok nafJacWinAdx.M := p521XHT_ok
  constructor
  · exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  iterate 3 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · constructor
    iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
    iterate 3 exact hT.constantTime (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
    exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · rw [← KeepReg.keeps_erase, ← KeepReg.keepsN_eq]
    simp only [Jacobian.jacAdd, Code.inline, Code.erase, Code.mapBlocks, hT.fprogB_mapBlocks]
    lit_decide
  · exact instrs_noClobber (by decide +kernel)

end VG.Proof.P521.X86_64

end

end

/-! Concrete timing checks and the doubler of P-521's baseline and ADX joint verification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P521
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.P521.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p521 publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTable_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p521x publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,nafTable_adx_checks,nafCacheTable_adx_ct,
    joint_adx_infinity_ct,joint_adx_counter_ct,fastGenerator_adx_checks,fastPeer_adx_checks⟩

theorem joint_doubler (hc : CfgOk p521) (hC : Weierstrass.Law p521.C) :
    JointDoubler publicJoint p521.C size (Joint.jacDouble publicJoint.K) :=
  jacDouble_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    jointDouble_ct joint_cached_checks.copy

theorem joint_adx_doubler (hc : CfgOk p521x) (hC : Weierstrass.Law p521x.C) :
    JointDoubler publicJointAdx p521x.C size (Joint.jacDouble publicJointAdx.K) :=
  jacDouble_doubler joint_adx_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    jointDouble_adx_ct joint_adx_cached_checks.copy

/-- `jointPrefix p521` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixErased : Prog isa := Code.erase (jointPrefix p521)

materialize_shared jointPrefixErased

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p521) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p521).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p521).inline

materialize_shared jointTailErased

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p521).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `jointPrefix p521x` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointPrefixAdxErased : Prog isa := Code.erase (jointPrefix p521x)

materialize_shared jointPrefixAdxErased

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p521x) :=
  VG.Taint.constantTime_mapBlocks (c' := jointPrefixAdxErased) taint_eraseInv (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- `(Cfg.jointTail p521x).inline` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def jointTailAdxErased : Prog isa := Code.erase (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p521x).inline

materialize_shared jointTailAdxErased

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p521x).inline :=
  VG.Taint.constantTime_mapBlocks (c' := jointTailAdxErased) taint_eraseInv (Taint.ofRegs [.rdi])
    rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P521
