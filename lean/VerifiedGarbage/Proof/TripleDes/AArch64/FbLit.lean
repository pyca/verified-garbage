import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Impl.TripleDes.AArch64.Fb

/-! # Triple DES-OFB, -CFB64 and -CFB8's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.TripleDes.AArch64.ofb
materialize_code Impl.TripleDes.AArch64.cfbEncrypt
materialize_code Impl.TripleDes.AArch64.cfbDecrypt
materialize_code Impl.TripleDes.AArch64.cfb8Encrypt
materialize_code Impl.TripleDes.AArch64.cfb8Decrypt

end VG
