module

public import VerifiedGarbage.Impl.X25519.AArch64.Base
public import VerifiedGarbage.Proof.Ed25519.AArch64.FixedBaseLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.X25519.AArch64.Base
meta import VerifiedGarbage.Proof.Ed25519.AArch64.FixedBaseLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # X25519 of the base point on AArch64: the code as a literal -/

@[expose] public section

namespace VG

materialize_code Impl.X25519.AArch64.Base.x25519Base

end VG
