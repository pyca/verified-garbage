import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
import VerifiedGarbage.Impl.Sm4.AArch64.Cbc

/-!
# SM4 on AArch64: the code as literals

The code of the key expansion, of ECB in both directions, of CTR and of CBC
in both directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again.
-/

namespace VG.Proof.Sm4.AArch64

materialize_flat_code expandKeyCode := Impl.Sm4.AArch64.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.AArch64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.AArch64.ecb .decrypt
materialize_flat_code ctrCode := Impl.Sm4.AArch64.ctr
materialize_flat_code cbcEncryptCode := Impl.Sm4.AArch64.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Sm4.AArch64.cbcDecrypt

end VG.Proof.Sm4.AArch64
