import VerifiedGarbage.Impl.P384.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import VerifiedGarbage.Proof.P384.X86_64.FieldTmpl

/-! Baseline and ADX taint checks of P-384's joint verifier's point additions.

The field arithmetic is checked without its displacements, as the
templates of its operations (`FieldTmpl`), each analysed once. -/
namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The window of the joint verifier, baseline and with ADX. -/
def nafJacWin := publicJoint.K
def nafJacWinAdx := publicJointAdx.K

theorem nafCachedJac_checks : CachedJacChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D 6160 := by
  have hT : p384T.Ok nafJacWin.M := p384HT_ok
  constructor
  iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCachedJac_adx_checks :
    CachedJacChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D 6160 := by
  have hT : p384XT.Ok nafJacWinAdx.M := p384XHT_ok
  constructor
  iterate 6 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_checks : JacMixedChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D := by
  have hT : p384T.Ok nafJacWin.M := p384HT_ok
  constructor
  iterate 5 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_adx_checks : JacMixedChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D := by
  have hT : p384XT.Ok nafJacWinAdx.M := p384XHT_ok
  constructor
  iterate 5 exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  iterate 3 exact hT.constantTimeB (by decide) (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) _ (by taint_decide)
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P384.X86_64
