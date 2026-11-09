module
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache

import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! A public cache lookup preserves the point and its Z²/Z³ relationships. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

def cachedSlots (n : Nat) (p : Pt) (dst : Nat) : List Nat := jacCoords p++[dst,dst+8*n]

end VG.Proof.Weierstrass.X86_64
