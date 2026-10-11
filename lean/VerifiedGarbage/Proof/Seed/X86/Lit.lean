import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Seed.X86.Ecb
import VerifiedGarbage.Impl.Seed.X86.ExpandKey

/-!
# SEED on x86 (32-bit): the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

namespace VG.Proof.Seed.X86

materialize_flat_code expandKeyCode := Impl.Seed.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Seed.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Seed.X86.ecb .decrypt

end VG.Proof.Seed.X86
