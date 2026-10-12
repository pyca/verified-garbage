import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Camellia.X86.Modes

/-!
# Camellia-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

namespace VG.Proof.Camellia.X86

materialize_flat_code cbcEncryptCode := Impl.Camellia.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Camellia.X86.cbcDecrypt

end VG.Proof.Camellia.X86
