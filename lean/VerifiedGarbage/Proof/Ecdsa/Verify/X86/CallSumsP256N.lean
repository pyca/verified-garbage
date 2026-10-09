import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Lit

/-!
# ECDSA verification over P-256 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

taint_summary p256MulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p256n.k Spec.Weierstrass.Mont.p256n.m)
taint_summary p256SubNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p256n.k Spec.Weierstrass.Mont.p256n.m)

end VG.Proof.Ecdsa.Verify.X86
