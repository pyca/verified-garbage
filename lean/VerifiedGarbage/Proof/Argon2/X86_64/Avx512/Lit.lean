import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512

/-! # Argon2 compression with AVX-512 as a checked instruction literal -/

namespace VG

materialize_code Impl.Argon2.X86_64.Avx512.compress

end VG
