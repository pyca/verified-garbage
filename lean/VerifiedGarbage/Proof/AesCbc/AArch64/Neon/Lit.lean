module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Neon
import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.AesCbc.AArch64.Neon
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # CBC decryption in AdvSIMD registers, as a literal -/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Neon
materialize_code decrypt
end VG.Impl.AesCbc.AArch64.Neon
