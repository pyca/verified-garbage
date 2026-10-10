import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey

/-!
# Camellia on X86_64: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again (seconds for the key expansion's).
-/

namespace VG.Proof.Camellia.X86_64

materialize_flat_code expandKeyCode := Impl.Camellia.X86_64.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.X86_64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.X86_64.ecb .decrypt

end VG.Proof.Camellia.X86_64
