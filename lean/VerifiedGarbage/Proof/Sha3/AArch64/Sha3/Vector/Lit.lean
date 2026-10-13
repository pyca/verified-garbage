module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
meta import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector
materialize_code permute
end VG.Impl.Sha3.AArch64.Sha3.Vector
