module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-! # Fused POWER8 AES-GCM code as a literal -/

@[expose] public section
namespace VG
materialize_code Impl.AesGcm.PPC64LE.Blocks.code
materialize_code Impl.AesGcm.PPC64LE.Blocks.encrypt
end VG
