module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
meta import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
materialize_code bulk
materialize_code body
end VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
