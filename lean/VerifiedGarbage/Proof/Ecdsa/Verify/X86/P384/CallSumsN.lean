module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P384.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ECDSA verification over P-384 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P384

open VG VG.X86

taint_summary mulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p384n.k Spec.Weierstrass.Mont.p384n.m)
taint_summary subNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p384n.k Spec.Weierstrass.Mont.p384n.m)

end VG.Proof.Ecdsa.Verify.X86.P384
