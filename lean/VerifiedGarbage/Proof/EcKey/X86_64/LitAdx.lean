import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.EcKey.P256.X86_64

/-!
# P-256 public keys on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies with BMI2 and ADX.
-/

namespace VG

materialize_code Impl.EcKey.X86_64.publicKeyP256Adx

end VG
