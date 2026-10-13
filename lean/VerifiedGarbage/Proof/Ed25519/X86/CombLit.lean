module

public import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.Comb
meta import VerifiedGarbage.Impl.Ed25519.X86.Comb
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! The comb as a literal (`materialize_code`): its field arithmetic is built once, here, rather
than in every check that evaluates it. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86

materialize_code combMultiply

end VG.Impl.Ed25519.X86
