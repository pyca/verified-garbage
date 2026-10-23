module

public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # CFB decryption code as a checked literal -/

@[expose] public section

namespace VG.Impl.AesCfb.AArch64.Decrypt
materialize_code code
end VG.Impl.AesCfb.AArch64.Decrypt
