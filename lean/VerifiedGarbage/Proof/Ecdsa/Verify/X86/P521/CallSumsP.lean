module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CallTaint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
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
# ECDSA verification over P-521 on x86 (32-bit): summaries of the field functions modulo `p`

See `CallTaint`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.P521

open VG VG.X86

taint_summary mulPSum : taint τV
  (Impl.Weierstrass.X86.Mont.mulFn Spec.Weierstrass.Mont.p521p.k Spec.Weierstrass.Mont.p521p.m)
taint_summary addPSum : taint τV
  (Impl.Weierstrass.X86.Mont.addFn Spec.Weierstrass.Mont.p521p.k Spec.Weierstrass.Mont.p521p.m)
taint_summary subPSum : taint τV
  (Impl.Weierstrass.X86.Mont.subFn Spec.Weierstrass.Mont.p521p.k Spec.Weierstrass.Mont.p521p.m)

end VG.Proof.Ecdsa.Verify.X86.P521
