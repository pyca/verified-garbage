module

public import VerifiedGarbage.Impl.Sm4.AArch64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
meta import VerifiedGarbage.Impl.Sm4.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # SM4-CFB128's and SM4-OFB's final functions' AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

materialize_code cfbEncryptFinalCode := Impl.Sm4.AArch64.cfbEncryptFinal
materialize_code cfbDecryptFinalCode := Impl.Sm4.AArch64.cfbDecryptFinal
materialize_code ofbFinalCode := Impl.Sm4.AArch64.ofbFinal

end VG.Proof.Sm4.AArch64
