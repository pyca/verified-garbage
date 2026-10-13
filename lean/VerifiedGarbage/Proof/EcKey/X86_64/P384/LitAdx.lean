module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.EcKey.P384.X86_64
meta import VerifiedGarbage.Impl.EcKey.P384.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# P-384 public keys on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies modulo `p` with BMI2 and ADX.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.X86_64.publicKeyP384Adx

end VG
