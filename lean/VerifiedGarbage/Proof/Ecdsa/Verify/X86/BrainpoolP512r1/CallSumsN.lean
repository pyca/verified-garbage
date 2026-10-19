module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# ECDSA verification over brainpoolP512r1 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.BrainpoolP512r1

open VG VG.X86

taint_summary mulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.brainpoolp512r1n.k Spec.Weierstrass.Mont.brainpoolp512r1n.m)
taint_summary subNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.brainpoolp512r1n.k Spec.Weierstrass.Mont.brainpoolp512r1n.m)

end VG.Proof.Ecdsa.Verify.X86.BrainpoolP512r1
