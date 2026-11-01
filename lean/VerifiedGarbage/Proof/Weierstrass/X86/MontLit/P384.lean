module

public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Weierstrass.X86.Mont
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Shared literals for P-384's x86 Montgomery calls

Materialize each operation once so callers can reuse its checked literal
instead of evaluating the unrolled instruction generator again.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.MontLit.P384

open VG

materialize_flat_code pMul := Impl.Weierstrass.X86.Mont.mulFn
  Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m
materialize_code pAdd := Impl.Weierstrass.X86.Mont.addFn
  Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m
materialize_code pSub := Impl.Weierstrass.X86.Mont.subFn
  Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m

materialize_flat_code nMul := Impl.Weierstrass.X86.Mont.mulFn
  Impl.Weierstrass.Mont.p384n.k Impl.Weierstrass.Mont.p384n.m
materialize_code nAdd := Impl.Weierstrass.X86.Mont.addFn
  Impl.Weierstrass.Mont.p384n.k Impl.Weierstrass.Mont.p384n.m
materialize_code nSub := Impl.Weierstrass.X86.Mont.subFn
  Impl.Weierstrass.Mont.p384n.k Impl.Weierstrass.Mont.p384n.m

end VG.Proof.Weierstrass.X86.MontLit.P384
