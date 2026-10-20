module

public import VerifiedGarbage.Impl.Argon2.AArch64.Initial
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.AArch64.Initial
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! A checked literal for the six-word H₀ header. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.Initial.headerCode

end VG
