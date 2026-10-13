module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ECDSA verification over P-256 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86

taint_summary p256MulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m)
taint_summary p256AddPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m)
taint_summary p256SubPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p256p.k Spec.Weierstrass.Mont.p256p.m)

end VG.Proof.Ecdsa.Verify.X86
