import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Seed.X86.Modes

/-!
# SEED-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

namespace VG.Proof.Seed.X86

materialize_flat_code cbcEncryptCode := Impl.Seed.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Seed.X86.cbcDecrypt

end VG.Proof.Seed.X86
