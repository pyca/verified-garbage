import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc

/-! # Triple DES-CBC's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.TripleDes.X86_64.cbcEncrypt
materialize_code Impl.TripleDes.X86_64.cbcDecrypt

end VG
