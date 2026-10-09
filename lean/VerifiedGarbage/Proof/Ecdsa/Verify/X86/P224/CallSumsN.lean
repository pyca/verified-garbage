import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Lit

/-!
# ECDSA verification over P-224 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

namespace VG.Proof.Ecdsa.Verify.X86.P224

open VG VG.X86

taint_summary mulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p224n.k Spec.Weierstrass.Mont.p224n.m)
taint_summary subNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p224n.k Spec.Weierstrass.Mont.p224n.m)

end VG.Proof.Ecdsa.Verify.X86.P224
