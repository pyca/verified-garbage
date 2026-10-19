module

import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.Comb
meta import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Ed25519.X86.PointMul
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! The comb as a literal (`materialize_code`): its field arithmetic is built once, here, rather
than in every check that evaluates it. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86

materialize_code combMultiply

end VG.Impl.Ed25519.X86
