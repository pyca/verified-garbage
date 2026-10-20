module

public import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Checked literal of the independent-address input header. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.AddressHeader.code

end VG
