module

public import VerifiedGarbage.Impl.Sha512.AArch64.Sha3
meta import VerifiedGarbage.Impl.Sha512.AArch64.Sha3
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Sha512.AArch64.Sha3
materialize_code compress
end VG.Impl.Sha512.AArch64.Sha3
