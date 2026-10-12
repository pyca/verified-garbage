import VerifiedGarbage.Proof.Cast5.X86_64.Lit
import VerifiedGarbage.Impl.Cast5.X86_64.Modes

/-! # CAST5-CBC, -OFB and -CFB64's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Cast5.X86_64.encryptBlock
materialize_value Impl.Cast5.X86_64.decryptBlock

/-! The functions. -/

materialize_code Impl.Cast5.X86_64.cbcEncrypt
materialize_code Impl.Cast5.X86_64.cbcDecrypt
materialize_code Impl.Cast5.X86_64.ofb
materialize_code Impl.Cast5.X86_64.cfbEncrypt
materialize_code Impl.Cast5.X86_64.cfbDecrypt

end VG
