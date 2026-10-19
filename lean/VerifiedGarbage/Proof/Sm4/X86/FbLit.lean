module

public import VerifiedGarbage.Impl.Sm4.X86.Fb
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Sm4.X86.Fb
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# SM4-OFB and SM4-CFB128 on x86 (32-bit): the code as literals

The code of OFB and CFB128 as literals (`materialize_flat_code`), which the
checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code ofbCode := Impl.Sm4.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Sm4.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Sm4.X86.cfbDecrypt

end VG.Proof.Sm4.X86
