import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2

/-! # Argon2 compression with AVX2 as a checked instruction literal -/

namespace VG

materialize_code Impl.Argon2.X86_64.Avx2.compress

end VG
