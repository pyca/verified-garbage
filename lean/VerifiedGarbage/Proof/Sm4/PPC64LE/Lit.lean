module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
public import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# SM4 on PPC64LE: the code as literals

The code of the key expansion, of ECB in both directions, and of the
preparation of the round keys and of a batch under them as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

materialize_code encKeyPair := Impl.Sm4.PPC64LE.keyPairsInline (.addi .r10 .r10 64) 1
materialize_code decKeyPair := Impl.Sm4.PPC64LE.keyPairsInline (.subi .r10 .r10 64) 1
materialize_code encKeyChunk := Impl.Sm4.PPC64LE.keyPairsInline (.addi .r10 .r10 64) 2
materialize_code decKeyChunk := Impl.Sm4.PPC64LE.keyPairsInline (.subi .r10 .r10 64) 2

materialize_code expandKeyCode := Impl.Sm4.PPC64LE.expandKey
materialize_code ecbEncrypt := Impl.Sm4.PPC64LE.ecb .encrypt
materialize_code ecbDecrypt := Impl.Sm4.PPC64LE.ecb .decrypt
materialize_code prepareKeysCode := Impl.Sm4.PPC64LE.prepareKeys
materialize_code cryptPreparedCode := Impl.Sm4.PPC64LE.cryptPrepared

end VG.Proof.Sm4.PPC64LE
