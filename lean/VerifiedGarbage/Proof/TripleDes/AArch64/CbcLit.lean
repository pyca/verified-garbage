import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc

/-! # Triple DES-CBC's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.TripleDes.AArch64.cbcEncrypt
materialize_code Impl.TripleDes.AArch64.cbcDecrypt

end VG
