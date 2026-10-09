import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey

/-!
# Camellia on AArch64: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again (seconds for the key expansion's).
-/

namespace VG.Proof.Camellia.AArch64

materialize_code expandKeyCode := Impl.Camellia.AArch64.expandKey
materialize_code ecbEncrypt := Impl.Camellia.AArch64.ecb .encrypt
materialize_code ecbDecrypt := Impl.Camellia.AArch64.ecb .decrypt

end VG.Proof.Camellia.AArch64
