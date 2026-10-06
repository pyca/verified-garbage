import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64

/-!
# ECDSA verification over P-256 on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies with BMI2 and ADX.
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.verifyP256Adx

end VG
