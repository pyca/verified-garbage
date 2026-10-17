module

import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-!
# ECDSA over P-256 on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies with BMI2 and ADX.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.X86_64.signP256Adx

end VG
