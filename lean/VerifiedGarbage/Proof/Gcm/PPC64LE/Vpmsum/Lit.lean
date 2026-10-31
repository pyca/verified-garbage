module

public import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
meta import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-! # POWER8 GHASH code as a literal -/

@[expose] public section
namespace VG
materialize_code Impl.Gcm.PPC64LE.Vpmsum.ghash
end VG
