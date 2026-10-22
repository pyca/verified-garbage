module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # CBC decryption code as a checked literal -/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Decrypt
materialize_code code
end VG.Impl.AesCbc.AArch64.Decrypt
