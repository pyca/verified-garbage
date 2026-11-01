module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
meta import VerifiedGarbage.Impl.Weierstrass.X86.Mont
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ECDSA verification over brainpoolP512r1 on x86 (32-bit): summaries of the field functions modulo `n`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.BrainpoolP512r1

open VG VG.X86

taint_summary mulNSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.brainpoolp512r1n.k Impl.Weierstrass.Mont.brainpoolp512r1n.m)
taint_summary subNSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.brainpoolp512r1n.k Impl.Weierstrass.Mont.brainpoolp512r1n.m)

end VG.Proof.Ecdsa.Verify.X86.BrainpoolP512r1
