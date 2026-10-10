import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Weierstrass.X86.Mont

/-!
# Shared literals for P-224's x86 Montgomery calls

Materialize each operation once so callers can reuse its checked literal
instead of evaluating the unrolled instruction generator again.
-/

namespace VG.Proof.Weierstrass.X86.MontLit.P224

open VG

materialize_flat_code pMul := Impl.Weierstrass.X86.Mont.mulFn
  Spec.Weierstrass.Mont.p224p.k Spec.Weierstrass.Mont.p224p.m
materialize_code pAdd := Impl.Weierstrass.X86.Mont.addFn
  Spec.Weierstrass.Mont.p224p.k Spec.Weierstrass.Mont.p224p.m
materialize_code pSub := Impl.Weierstrass.X86.Mont.subFn
  Spec.Weierstrass.Mont.p224p.k Spec.Weierstrass.Mont.p224p.m

materialize_flat_code nMul := Impl.Weierstrass.X86.Mont.mulFn
  Spec.Weierstrass.Mont.p224n.k Spec.Weierstrass.Mont.p224n.m
materialize_code nAdd := Impl.Weierstrass.X86.Mont.addFn
  Spec.Weierstrass.Mont.p224n.k Spec.Weierstrass.Mont.p224n.m
materialize_code nSub := Impl.Weierstrass.X86.Mont.subFn
  Spec.Weierstrass.Mont.p224n.k Spec.Weierstrass.Mont.p224n.m

end VG.Proof.Weierstrass.X86.MontLit.P224
