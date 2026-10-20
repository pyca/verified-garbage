module

public import VerifiedGarbage.Impl.Sm4.X86.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.X86.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SM4-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code cbcEncryptChainedCode := Impl.Sm4.X86.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Sm4.X86.cbcDecryptChained

end VG.Proof.Sm4.X86
