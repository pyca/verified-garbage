module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # CBC encryption code as a checked literal -/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Encrypt
materialize_code code
end VG.Impl.AesCbc.AArch64.Encrypt
