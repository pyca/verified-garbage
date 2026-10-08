import VerifiedGarbage.Proof.P256.EcdhJac.Frame

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

/-- The window computation writes only its declared work areas. Its output
is the existing project's homogeneous point representation. Invalid scalars
need no multiplication identity because the public API rejects them. -/
structure WindowPost (base : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  frame : Frame base buildWork s t
  field : Inv M base 8192 C.p Sl live (tmv C 4 base t) t
  point : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)

end VG.Proof.P256.EcdhJac
