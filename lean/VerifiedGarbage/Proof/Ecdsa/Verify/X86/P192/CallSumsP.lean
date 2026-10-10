import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P192.Lit

/-!
# ECDSA verification over P-192 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

namespace VG.Proof.Ecdsa.Verify.X86.P192

open VG VG.X86

taint_summary mulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p192p.k Spec.Weierstrass.Mont.p192p.m)
taint_summary addPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.p192p.k Spec.Weierstrass.Mont.p192p.m)
taint_summary subPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p192p.k Spec.Weierstrass.Mont.p192p.m)

end VG.Proof.Ecdsa.Verify.X86.P192
