module

public import VerifiedGarbage.Impl.P224.X86_64.Joint
meta import VerifiedGarbage.Impl.P224.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
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

/-! Taint checks of P-224's joint verifier's point additions. -/

@[expose] public section

namespace VG.Proof.P224.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.P224.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The window of the joint verifier. -/
def nafJacWin := publicJoint.K

theorem nafCachedJac_checks : CachedJacChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D 5408 := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafMixedJac_checks : JacMixedChecks nafJacWin nafJacWin.R nafJacWin.E nafJacWin.D := by
  constructor <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P224.X86_64
