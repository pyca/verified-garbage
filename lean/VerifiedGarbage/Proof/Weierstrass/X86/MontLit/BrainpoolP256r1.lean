module

public import VerifiedGarbage.Impl.Weierstrass.X86.Mont
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Weierstrass.X86.Mont
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

/-!
# Shared literals for brainpoolP256r1's x86 Montgomery calls

Materialize each operation once so callers can reuse its checked literal
instead of evaluating the unrolled instruction generator again.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1

open VG

materialize_flat_code pMul := Impl.Weierstrass.X86.Mont.mulFn
  Spec.Weierstrass.Mont.brainpoolp256r1p.k Spec.Weierstrass.Mont.brainpoolp256r1p.m
materialize_code pAdd := Impl.Weierstrass.X86.Mont.addFn
  Spec.Weierstrass.Mont.brainpoolp256r1p.k Spec.Weierstrass.Mont.brainpoolp256r1p.m
materialize_code pSub := Impl.Weierstrass.X86.Mont.subFn
  Spec.Weierstrass.Mont.brainpoolp256r1p.k Spec.Weierstrass.Mont.brainpoolp256r1p.m

materialize_flat_code nMul := Impl.Weierstrass.X86.Mont.mulFn
  Spec.Weierstrass.Mont.brainpoolp256r1n.k Spec.Weierstrass.Mont.brainpoolp256r1n.m
materialize_code nAdd := Impl.Weierstrass.X86.Mont.addFn
  Spec.Weierstrass.Mont.brainpoolp256r1n.k Spec.Weierstrass.Mont.brainpoolp256r1n.m
materialize_code nSub := Impl.Weierstrass.X86.Mont.subFn
  Spec.Weierstrass.Mont.brainpoolp256r1n.k Spec.Weierstrass.Mont.brainpoolp256r1n.m

end VG.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
