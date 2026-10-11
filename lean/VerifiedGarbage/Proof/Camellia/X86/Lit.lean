import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Camellia.X86.Ecb
import VerifiedGarbage.Impl.Camellia.X86.ExpandKey

/-!
# Camellia on x86 (32-bit): the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

namespace VG.Proof.Camellia.X86

materialize_flat_code expandKeyCode := Impl.Camellia.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.X86.ecb .decrypt

end VG.Proof.Camellia.X86
