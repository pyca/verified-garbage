module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Blocks
meta import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32
meta import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-! # POWER8 AES code as literals -/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE
materialize_code ctr32
materialize_code encryptBlocks
materialize_code decryptBlocks
materialize_code expandKey
end VG.Impl.Aes.PPC64LE
