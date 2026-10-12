import VerifiedGarbage.Proof.Cast5.AArch64.Lit
import VerifiedGarbage.Impl.Cast5.AArch64.Modes

/-! # CAST5-CBC, -OFB and -CFB64's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Cast5.AArch64.encryptBlock
materialize_value Impl.Cast5.AArch64.decryptBlock

/-! The functions. -/

materialize_code Impl.Cast5.AArch64.cbcEncrypt
materialize_code Impl.Cast5.AArch64.cbcDecrypt
materialize_code Impl.Cast5.AArch64.ofb
materialize_code Impl.Cast5.AArch64.cfbEncrypt
materialize_code Impl.Cast5.AArch64.cfbDecrypt

end VG
