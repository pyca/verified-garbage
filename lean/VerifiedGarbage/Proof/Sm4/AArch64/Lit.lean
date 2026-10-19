module

public import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
public import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
meta import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# SM4 on AArch64: the code as literals

The code of the key expansion, of ECB in both directions, of the preparation
of the round keys and of a batch under them, of CTR and of CBC in both
directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

materialize_flat_code expandKeyCode := Impl.Sm4.AArch64.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.AArch64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.AArch64.ecb .decrypt
materialize_flat_code ecbAnyCode := Impl.Sm4.AArch64.ecbAny
materialize_flat_code prepareKeysCode := Impl.Sm4.AArch64.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Sm4.AArch64.cryptPrepared
materialize_flat_code ctrCode := Impl.Sm4.AArch64.ctr
materialize_flat_code cbcEncryptChainedCode := Impl.Sm4.AArch64.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Sm4.AArch64.cbcDecryptChained

end VG.Proof.Sm4.AArch64
