module

public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
meta import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# AES on RISC-V, as literals

The code of `vg_aes_ctr32`, `vg_aes_{en,de}crypt_blocks` and
`vg_aes_expand_key_scratch`, built by functions, as literals
(`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`, here and in the modes that call it) read the literal instead
of building the code again.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

materialize_code ctr32
materialize_code encryptBlocks
materialize_code decryptBlocks
materialize_code expandKey

end VG.Impl.Aes.RISCV64
