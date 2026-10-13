module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
meta import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! The kernel checks this literal once; taint and instruction checks reuse it. -/

@[expose] public section

namespace VG
materialize_code Impl.Ed25519.AArch64.scalarReduce
end VG
