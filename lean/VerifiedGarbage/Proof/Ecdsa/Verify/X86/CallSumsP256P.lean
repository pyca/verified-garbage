import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Lit

/-!
# ECDSA verification over P-256 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

taint_summary p256MulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m)
taint_summary p256AddPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m)
taint_summary p256SubPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m)

end VG.Proof.Ecdsa.Verify.X86
