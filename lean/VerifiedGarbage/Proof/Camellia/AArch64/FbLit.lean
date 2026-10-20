module

public import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Camellia-OFB and Camellia-CFB128 on AArch64: the code as literals

As `Lit.lean`, for the feedback modes.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

materialize_flat_code ofbCode := Impl.Camellia.AArch64.ofb
materialize_flat_code cfbEncryptCode := Impl.Camellia.AArch64.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Camellia.AArch64.cfbDecrypt

end VG.Proof.Camellia.AArch64
