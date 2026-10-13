module

public import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulTaint
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
