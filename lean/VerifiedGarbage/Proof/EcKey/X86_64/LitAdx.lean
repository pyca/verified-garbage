module

import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Impl.EcKey.P256.X86_64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Impl.EcKey.P256.X86_64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# P-256 public keys on x86-64 with BMI2 and ADX: the code as a literal

As `Lit.lean`, for the code that multiplies with BMI2 and ADX.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.X86_64.publicKeyP256Adx

end VG
