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
# ECDSA verification over P-521 on x86 (32-bit): summaries of the field functions modulo `p`, called from the point functions

See `CallTaint`: the point functions call the field functions one frame below
the verifier's own calls of them (`τVPoint`), where the summaries of
`CallSumsP` (from `τVTop`) do not apply, and each such call was analysed in
full.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P521

open VG VG.X86

taint_summary mulPPointSum : taint τVPoint
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary addPPointSum : taint τVPoint
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary subPPointSum : taint τVPoint
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)

end VG.Proof.Ecdsa.Verify.X86.P521
