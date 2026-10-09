import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Lit

/-!
# ECDSA verification over P-224 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

namespace VG.Proof.Ecdsa.Verify.X86.P224

open VG VG.X86

taint_summary mulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p224p.k Spec.Weierstrass.Mont.p224p.m)
taint_summary addPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.p224p.k Spec.Weierstrass.Mont.p224p.m)
taint_summary subPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p224p.k Spec.Weierstrass.Mont.p224p.m)

end VG.Proof.Ecdsa.Verify.X86.P224
