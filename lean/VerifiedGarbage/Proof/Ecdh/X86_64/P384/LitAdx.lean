import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdh.P384.X86_64

/-!
# ECDH over P-384 on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies modulo `p` with BMI2 and ADX.
-/

namespace VG

materialize_code Impl.Ecdh.X86_64.exchangeP384Adx

end VG
