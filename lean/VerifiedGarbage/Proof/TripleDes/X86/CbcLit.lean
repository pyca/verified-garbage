import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
import VerifiedGarbage.Impl.TripleDes.X86.Modes

/-!
# Triple DES-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals (`materialize_code`),
which the checks of the whole functions (`taint_decide`, `lit_decide`) read
rather than build the code again.
-/

namespace VG

materialize_code Impl.TripleDes.X86.cbcEncrypt
materialize_code Impl.TripleDes.X86.cbcDecrypt

end VG
