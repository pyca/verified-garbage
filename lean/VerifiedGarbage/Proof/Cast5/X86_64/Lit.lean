import VerifiedGarbage.Impl.Cast5.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`, the ABI). -/
namespace VG.Impl.Cast5.X86_64
materialize_code ecbEncrypt
materialize_code ecbDecrypt
materialize_code expandKey
end VG.Impl.Cast5.X86_64
