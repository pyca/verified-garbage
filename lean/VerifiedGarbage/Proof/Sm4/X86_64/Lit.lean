module

public import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
meta import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

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

materialize_flat_code expandKeyCode := Impl.Sm4.X86_64.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.X86_64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.X86_64.ecb .decrypt
materialize_flat_code cryptPreparedCode := Impl.Sm4.X86_64.cryptPrepared

end VG.Proof.Sm4.X86_64
