module

public import VerifiedGarbage.Impl.X25519.X86_64.Base
meta import VerifiedGarbage.Impl.X25519.X86_64.Base
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit

/-! Checked literals for fixed-base X25519. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.Impl.X25519.X86_64
materialize_code baseLit := (Base.x25519Base baseline)
materialize_code baseAdxLit := (Base.x25519Base adx)
materialize_code baseAdxYLit := Base.x25519BaseAdx
end VG.Proof.X25519.X86_64.Base
