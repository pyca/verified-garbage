import VerifiedGarbage.Impl.P521.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming

/-! Baseline and ADX taint checks of P-521's joint verifier's point additions. -/
namespace VG.Proof.P521.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.P521.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The window of the joint verifier, baseline and with ADX. -/
def nafJacWin := publicJoint.K
def nafJacWinAdx := publicJointAdx.K

theorem nafCachedJac_checks : CachedJacChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D 5040 := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCachedJac_adx_checks :
    CachedJacChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D 5040 := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_checks : JacMixedChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_adx_checks : JacMixedChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P521.X86_64
