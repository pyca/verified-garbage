module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
meta import VerifiedGarbage.Impl.Weierstrass.X86.Mont
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ECDSA verification over P-521 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P521

open VG VG.X86

taint_summary mulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p521n.k Spec.Weierstrass.Mont.p521n.m)
taint_summary subNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p521n.k Spec.Weierstrass.Mont.p521n.m)

end VG.Proof.Ecdsa.Verify.X86.P521
