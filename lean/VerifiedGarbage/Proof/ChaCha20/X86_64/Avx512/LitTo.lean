import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512To

/-!
# ChaCha20 out of place on x86-64 with AVX-512: the code as a literal
-/

namespace VG

materialize_code Impl.ChaCha20.X86_64.Avx512.xorTo

end VG
