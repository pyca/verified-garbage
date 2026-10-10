import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey
import VerifiedGarbage.Impl.Camellia.AArch64.Ctr

/-!
# Camellia on AArch64: the code as literals

The code of the key expansion, of ECB in both directions and of CTR as
literals (`materialize_code`, `Proof/Framework/Lit.lean`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again (seconds for the key expansion's).
-/

namespace VG.Proof.Camellia.AArch64

materialize_flat_code expandKeyCode := Impl.Camellia.AArch64.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.AArch64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.AArch64.ecb .decrypt
materialize_flat_code ctrCode := Impl.Camellia.AArch64.ctr

end VG.Proof.Camellia.AArch64
