module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Blocks
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Aes.AArch64.Neon.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES bitsliced in AdvSIMD registers on AArch64: the entry points, as literals

The code of the block functions, built by functions, as literals
(`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`, the registration files' `spSafe`) read the literal instead
of building the code again.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.AArch64.Neon
