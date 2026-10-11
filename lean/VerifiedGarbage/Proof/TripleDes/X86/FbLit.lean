import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.TripleDes.X86.Fb

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86 (32-bit): the code as literals

The code of the functions as literals (`materialize_code`), which the checks
of the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again.
-/

namespace VG

materialize_code Impl.TripleDes.X86.ofb
materialize_code Impl.TripleDes.X86.cfbEncrypt
materialize_code Impl.TripleDes.X86.cfbDecrypt
materialize_code Impl.TripleDes.X86.cfb8Encrypt
materialize_code Impl.TripleDes.X86.cfb8Decrypt

end VG
