import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Impl.Sm4.AArch64.Fb

/-!
# SM4-OFB and SM4-CFB128 on AArch64: the code as literals

As `Lit.lean`, for the feedback modes.
-/

namespace VG.Proof.Sm4.AArch64

materialize_flat_code ofbCode := Impl.Sm4.AArch64.ofb
materialize_flat_code cfbEncryptCode := Impl.Sm4.AArch64.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Sm4.AArch64.cfbDecrypt

end VG.Proof.Sm4.AArch64
