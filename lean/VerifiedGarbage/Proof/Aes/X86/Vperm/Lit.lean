module

public import VerifiedGarbage.Impl.Aes.X86.Vperm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.Aes.X86.Vperm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # AES by vector permutations on x86 (32-bit): the code as literals -/

@[expose] public section

namespace VG.Impl.Aes.X86.Vperm
materialize_code encryptBlocks
materialize_code decryptBlocks
materialize_code ctr32To
end VG.Impl.Aes.X86.Vperm
