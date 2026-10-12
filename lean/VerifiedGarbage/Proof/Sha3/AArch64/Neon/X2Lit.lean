module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.X2
materialize_code neon := code false
materialize_code sha3 := code true
end VG.Impl.Sha3.AArch64.Neon.X2
