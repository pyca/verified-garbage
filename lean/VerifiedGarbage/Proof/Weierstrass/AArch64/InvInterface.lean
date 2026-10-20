module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

/-! Curves using a public early-exit inverse also supply its Montgomery-form
arithmetic theorem. This proof-only interface leaves contracts and the TCB unchanged. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

structure HasLawInvToM (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  invToM : InvToM C.n

/-- Curves whose windows in Jacobian coordinates use the prime-order
separation theorem (`windowJ_ok`). -/
structure HasLawInvOrd (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  prime : PrimeOrder C

/-- Curves whose secret window additions use the prime-order separation theorem. -/
structure HasLawInvToMOrd (C : Spec.Weierstrass.Curve) extends HasLawInvToM C where
  prime : PrimeOrder C
  /-- Arithmetic correctness used by the packed field inversion. -/
  invToMP : InvToM C.p

end VG.Proof.Weierstrass.AArch64
