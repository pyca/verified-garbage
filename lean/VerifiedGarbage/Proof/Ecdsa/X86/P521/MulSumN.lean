module

public import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulTaint
public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Spec.Weierstrass.Point
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulTaint
meta import VerifiedGarbage.Impl.Weierstrass.X86.Mont
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Weierstrass.Point

/-!
# ECDSA over P-521 on x86 (32-bit): the summary of the multiplication modulo `n`

See `MulTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P521

open VG VG.X86

taint_summary mulNSum : taint τMul
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p521n.k Spec.Weierstrass.Mont.p521n.m)

end VG.Proof.Ecdsa.X86.P521
