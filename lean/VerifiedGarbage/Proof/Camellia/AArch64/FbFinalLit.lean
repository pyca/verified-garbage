module

public import VerifiedGarbage.Impl.Camellia.AArch64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
meta import VerifiedGarbage.Impl.Camellia.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Camellia-CFB128's and Camellia-OFB's final functions' AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

materialize_code cfbEncryptFinalCode := Impl.Camellia.AArch64.cfbEncryptFinal
materialize_code cfbDecryptFinalCode := Impl.Camellia.AArch64.cfbDecryptFinal
materialize_code ofbFinalCode := Impl.Camellia.AArch64.ofbFinal

end VG.Proof.Camellia.AArch64
