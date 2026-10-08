import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-!
# ECDSA over P-384 on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies modulo `p` with BMI2 and ADX.
-/

namespace VG

materialize_code Impl.Ecdsa.X86_64.signP384Adx

end VG
