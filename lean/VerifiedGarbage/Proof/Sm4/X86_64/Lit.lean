module

public import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SM4 on X86_64: the code as literals

The code of the key expansion, of ECB in both directions and of
`vg_sm4_crypt_prepared` as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

materialize_code expandKeyCode := Impl.Sm4.X86_64.expandKey
materialize_code ecbEncrypt := Impl.Sm4.X86_64.ecb .encrypt
materialize_code ecbDecrypt := Impl.Sm4.X86_64.ecb .decrypt
materialize_code cryptPreparedCode := Impl.Sm4.X86_64.cryptPrepared

materialize_code ecbSharedEncrypt := Impl.Sm4.X86_64.ecbShared .encrypt
materialize_code ecbSharedDecrypt := Impl.Sm4.X86_64.ecbShared .decrypt
materialize_code ecbSharedEncryptInline := (Impl.Sm4.X86_64.ecbShared .encrypt).inline
materialize_code ecbSharedDecryptInline := (Impl.Sm4.X86_64.ecbShared .decrypt).inline

end VG.Proof.Sm4.X86_64
