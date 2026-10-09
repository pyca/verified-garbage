import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit

/-!
# ECDSA verification over P-521 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

namespace VG.Proof.Ecdsa.Verify.X86.P521

open VG VG.X86

taint_summary mulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p521n.k Spec.Weierstrass.Mont.p521n.m)
taint_summary subNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p521n.k Spec.Weierstrass.Mont.p521n.m)

end VG.Proof.Ecdsa.Verify.X86.P521
