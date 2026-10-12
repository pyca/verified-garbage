module

public import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulTaint
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ECDSA over P-521 on x86 (32-bit): the summary of the multiplication modulo `p`

See `MulTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P521

open VG VG.X86

taint_summary mulPSum : taint τMul
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p521p.k Spec.Weierstrass.Mont.p521p.m)

end VG.Proof.Ecdsa.X86.P521
