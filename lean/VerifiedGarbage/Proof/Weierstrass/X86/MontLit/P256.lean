module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
meta import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Shared literals for P-256's x86 Montgomery calls

Materialize each operation once so callers can reuse its checked literal
instead of evaluating the unrolled instruction generator again.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.MontLit.P256

open VG

materialize_code pMul := Impl.Weierstrass.X86.Mont.mulFn
  Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m
materialize_code pAdd := Impl.Weierstrass.X86.Mont.addFn
  Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m
materialize_code pSub := Impl.Weierstrass.X86.Mont.subFn
  Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m

materialize_code nMul := Impl.Weierstrass.X86.Mont.mulFn
  Spec.Weierstrass.Mont.p256n.k Spec.Weierstrass.Mont.p256n.m
materialize_code nAdd := Impl.Weierstrass.X86.Mont.addFn
  Spec.Weierstrass.Mont.p256n.k Spec.Weierstrass.Mont.p256n.m
materialize_code nSub := Impl.Weierstrass.X86.Mont.subFn
  Spec.Weierstrass.Mont.p256n.k Spec.Weierstrass.Mont.p256n.m

end VG.Proof.Weierstrass.X86.MontLit.P256
