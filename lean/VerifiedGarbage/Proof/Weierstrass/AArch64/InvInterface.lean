import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.InvToM

/-! Curves using a public early-exit inverse also supply its Montgomery-form
arithmetic theorem. This proof-only interface leaves contracts and the TCB unchanged. -/
namespace VG.Proof.Weierstrass.AArch64

structure HasLawInvToM (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  invToM : InvToM C.n

end VG.Proof.Weierstrass.AArch64
