module

import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.Comb
public import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Impl.Ed25519.X86.Comb
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! The comb as a literal (`materialize_code`): its field arithmetic is built once, here, rather
than in every check that evaluates it. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86

materialize_code combMultiply

end VG.Impl.Ed25519.X86
