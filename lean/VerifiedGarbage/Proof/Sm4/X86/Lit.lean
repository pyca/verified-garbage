module

public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Impl.Sm4.X86.Prepared
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.X86.Prepared
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SM4 on x86 (32-bit): the code as literals

The code of the key expansion, of ECB in both directions, and of the
preparation of the round keys and a batch under them as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code expandKeyCode := Impl.Sm4.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.X86.ecb .decrypt
materialize_flat_code prepareKeysCode := Impl.Sm4.X86.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Sm4.X86.cryptPrepared

end VG.Proof.Sm4.X86
