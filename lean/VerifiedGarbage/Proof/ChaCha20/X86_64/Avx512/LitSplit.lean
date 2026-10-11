import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split

/-!
# ChaCha20 with the data's first bytes from another buffer on x86-64 with AVX-512: the code as a literal
-/

namespace VG

materialize_code Impl.ChaCha20.X86_64.Avx512.xorSplit

end VG
