module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
meta import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG
materialize_code Impl.Poly1305.AArch64.Radix64.blocks
materialize_code Impl.Poly1305.AArch64.Radix64.update
materialize_code Impl.Poly1305.AArch64.Radix64.finalize
end VG
