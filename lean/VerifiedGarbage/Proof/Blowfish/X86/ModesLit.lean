import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Blowfish.X86.Modes

/-!
# Blowfish's modes on x86 (32-bit): the code as literals

The code of CBC, OFB and CFB64 as literals (`materialize_flat_code`), which
the checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

namespace VG.Proof.Blowfish.X86

materialize_flat_code cbcEncryptCode := Impl.Blowfish.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Blowfish.X86.cbcDecrypt
materialize_flat_code ofbCode := Impl.Blowfish.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Blowfish.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Blowfish.X86.cfbDecrypt

end VG.Proof.Blowfish.X86
