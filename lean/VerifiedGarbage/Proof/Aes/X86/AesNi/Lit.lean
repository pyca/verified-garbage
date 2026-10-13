module

public import VerifiedGarbage.Impl.Aes.X86.AesNi
meta import VerifiedGarbage.Impl.Aes.X86.AesNi
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Aes.X86.AesNi
materialize_code expandKey
materialize_code ctr32
end VG.Impl.Aes.X86.AesNi
