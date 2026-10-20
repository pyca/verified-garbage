module

public import VerifiedGarbage.Impl.Cast5.X86.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# CAST5-CBC, -OFB and -CFB64 on x86 (32-bit): the code as literals

The code of the modes over CAST5's core as literals (`materialize_flat_code`),
which the checks of the whole functions (`taint_decide`, `lit_decide`) read
rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

materialize_flat_code cbcEncryptChainedCode := Impl.Cast5.X86.Modes.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Cast5.X86.Modes.cbcDecryptChained
materialize_flat_code ofbCode := Impl.Cast5.X86.Modes.ofb
materialize_flat_code cfbEncryptCode := Impl.Cast5.X86.Modes.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Cast5.X86.Modes.cfbDecrypt

end VG.Proof.Cast5.X86
