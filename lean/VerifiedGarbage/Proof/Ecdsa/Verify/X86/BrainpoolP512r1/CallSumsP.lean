module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ECDSA verification over brainpoolP512r1 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.BrainpoolP512r1

open VG VG.X86

taint_summary mulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.brainpoolp512r1p.k Spec.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary addPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.brainpoolp512r1p.k Spec.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary subPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.brainpoolp512r1p.k Spec.Weierstrass.Mont.brainpoolp512r1p.m)

end VG.Proof.Ecdsa.Verify.X86.BrainpoolP512r1
