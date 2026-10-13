module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P192.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P192.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ECDSA verification over P-192 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P192

open VG VG.X86

taint_summary mulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p192p.k Spec.Weierstrass.Mont.p192p.m)
taint_summary addPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.p192p.k Spec.Weierstrass.Mont.p192p.m)
taint_summary subPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p192p.k Spec.Weierstrass.Mont.p192p.m)

end VG.Proof.Ecdsa.Verify.X86.P192
