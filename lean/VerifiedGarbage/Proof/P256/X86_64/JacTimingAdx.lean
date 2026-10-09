import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming

/-! Concrete checks for the public verifier's point operations with BMI2 and ADX
(baseline: `JacTiming`). -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

def nafJacWinAdx := p256x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

theorem nafCachedJac_adx_checks :
    CachedJacChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D 5408 := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_adx_checks : JacMixedChecks nafJacWinAdx nafJacWinAdx.R nafJacWinAdx.E nafJacWinAdx.D := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
