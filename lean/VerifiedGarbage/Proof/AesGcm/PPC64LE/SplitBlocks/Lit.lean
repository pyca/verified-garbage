module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-! # Source-prefix POWER8 AES-GCM code as literals -/

@[expose] public section
namespace VG
materialize_code Impl.AesGcm.PPC64LE.SplitBlocks.load
materialize_code Impl.AesGcm.PPC64LE.SplitBlocks.code
materialize_code Impl.AesGcm.PPC64LE.SplitBlocks.head
materialize_code Impl.AesGcm.PPC64LE.SplitBlocks.rest
materialize_code Impl.AesGcm.PPC64LE.SplitBlocks.encrypt
end VG
