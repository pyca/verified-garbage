module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2
meta import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Argon2 compression with AVX2 as a checked instruction literal -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.Avx2.compress

end VG
