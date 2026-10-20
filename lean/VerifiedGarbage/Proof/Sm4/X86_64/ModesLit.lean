module

public import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
public import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
meta import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
public import VerifiedGarbage.Impl.Sm4.X86_64.Fb
meta import VerifiedGarbage.Impl.Sm4.X86_64.Fb
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
# SM4's modes on x86-64: the code as literals

As `Lit.lean`, for CBC, CTR, OFB and CFB128, whose code the checks of the
whole functions (`taint_decide`, `lit_decide`: the ABI, the stack scratch
and `spSafe`) evaluate several times each.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

materialize_flat_code cbcEncryptChainedCode := Impl.Sm4.X86_64.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Sm4.X86_64.cbcDecryptChained
materialize_flat_code ctrCode := Impl.Sm4.X86_64.ctr
materialize_flat_code ofbCode := Impl.Sm4.X86_64.ofb
materialize_flat_code cfbEncryptCode := Impl.Sm4.X86_64.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Sm4.X86_64.cfbDecrypt

end VG.Proof.Sm4.X86_64
