module

public import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Aes.AArch64.Blocks
meta import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES on AArch64: the entry points, as literals

The code of the key expansion, CTR32 and the block functions, in their
bitsliced and AESE forms, built by functions, as literals
(`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`, the registration file's `spSafe`) read the literal instead of
building the code again.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64
materialize_code expandKey
materialize_code ctr32
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.AArch64

namespace VG.Impl.Aes.AArch64.Aese
materialize_code expandKey
materialize_code ctr32
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.AArch64.Aese
