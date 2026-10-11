import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Impl.Camellia.AArch64.Fb

/-!
# Camellia-OFB and Camellia-CFB128 on AArch64: the code as literals

As `Lit.lean`, for the feedback modes.
-/

namespace VG.Proof.Camellia.AArch64

materialize_flat_code ofbCode := Impl.Camellia.AArch64.ofb
materialize_flat_code cfbEncryptCode := Impl.Camellia.AArch64.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Camellia.AArch64.cfbDecrypt

end VG.Proof.Camellia.AArch64
