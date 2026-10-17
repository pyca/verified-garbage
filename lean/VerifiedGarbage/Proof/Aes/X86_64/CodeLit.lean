module

public import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
meta import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
public import VerifiedGarbage.Impl.Aes.X86_64.Blocks
meta import VerifiedGarbage.Impl.Aes.X86_64.Blocks
public import VerifiedGarbage.Impl.Aes.X86_64.AesNi
meta import VerifiedGarbage.Impl.Aes.X86_64.AesNi
public import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks
meta import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks
public import VerifiedGarbage.Impl.Aes.X86_64.Vaes
meta import VerifiedGarbage.Impl.Aes.X86_64.Vaes
public import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks
meta import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# AES on x86-64: the CTR32 and block functions, as literals

The code of `vg_aes_ctr32` and `vg_aes_{en,de}crypt_blocks`, in their scalar,
AES-NI and VAES forms, built by functions, as literals (`materialize_code`):
the checks that evaluate it (`lit_decide`, `taint_decide`, the registration
file's `spSafe`) read the literal instead of building the code again.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64
materialize_code ctr32
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.X86_64

namespace VG.Impl.Aes.X86_64.AesNi
materialize_code ctr32
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.X86_64.AesNi

namespace VG.Impl.Aes.X86_64.Vaes
materialize_code ctr32
end VG.Impl.Aes.X86_64.Vaes

namespace VG.Impl.Aes.X86_64.VaesBlocks
materialize_code encryptBlocks
materialize_code decryptBlocks
end VG.Impl.Aes.X86_64.VaesBlocks
