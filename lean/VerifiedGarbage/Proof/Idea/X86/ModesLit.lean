import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Idea.X86.Modes

/-!
# IDEA's modes on x86 (32-bit): the code as literals

The code of CBC, OFB and CFB64 as literals (`materialize_flat_code`), which
the checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

namespace VG.Proof.Idea.X86

materialize_flat_code cbcEncryptCode := Impl.Idea.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Idea.X86.cbcDecrypt
materialize_flat_code ofbCode := Impl.Idea.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Idea.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Idea.X86.cfbDecrypt

end VG.Proof.Idea.X86
