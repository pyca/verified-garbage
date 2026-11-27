module

public import VerifiedGarbage.Impl.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # X25519 on AArch64: the ladder's code as a literal -/

@[expose] public section

namespace VG

materialize_code Impl.X25519.AArch64.Ladder.x25519

end VG
