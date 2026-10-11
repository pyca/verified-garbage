import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sm4.X86.Modes

/-!
# SM4-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

namespace VG.Proof.Sm4.X86

materialize_flat_code cbcEncryptCode := Impl.Sm4.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Sm4.X86.cbcDecrypt

end VG.Proof.Sm4.X86
