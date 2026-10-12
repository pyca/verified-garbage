module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
meta import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Checked literal of the independent-address input header. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.AddressHeader.code

end VG
