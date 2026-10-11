import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Impl.TripleDes.X86_64.Fb

/-! # Triple DES-OFB, -CFB64 and -CFB8's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.TripleDes.X86_64.ofb
materialize_code Impl.TripleDes.X86_64.cfbEncrypt
materialize_code Impl.TripleDes.X86_64.cfbDecrypt
materialize_code Impl.TripleDes.X86_64.cfb8Encrypt
materialize_code Impl.TripleDes.X86_64.cfb8Decrypt

end VG
