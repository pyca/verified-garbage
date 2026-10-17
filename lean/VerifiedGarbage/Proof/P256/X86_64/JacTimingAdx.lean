module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Ecdsa.Generic

/-! Concrete checks for the public verifier's point operations with BMI2 and ADX
(baseline: `JacTiming`). -/

@[expose] public section

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
