import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit

/-! The comb as a literal (`materialize_code`): its field arithmetic is built once, here, rather
than in every check that evaluates it. -/
namespace VG.Impl.Ed25519.X86

materialize_code combMultiply

end VG.Impl.Ed25519.X86
