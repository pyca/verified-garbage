import VerifiedGarbage.Impl.Cast5.Arm
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`). -/
namespace VG.Impl.Cast5.Arm
materialize_table sL 9
materialize_table tab1234Nat 1024
materialize_code scan1234
materialize_code ecbEncrypt
materialize_code ecbDecrypt
materialize_table tab5678Nat 1024
materialize_code scan5678
materialize_code expandKey
end VG.Impl.Cast5.Arm
