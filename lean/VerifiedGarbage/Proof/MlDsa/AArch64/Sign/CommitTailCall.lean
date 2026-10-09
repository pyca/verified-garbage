import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

theorem callee65 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48)
      (commitTailContract AArch64.abi 768 48 S) :=
  CalleeOk.of_verified hS verified65 (by omega) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48).aarch64Depth=0 := by decide
    rw [h]; omega)

theorem callee87 {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64)
      (commitTailContract AArch64.abi 1024 64 S) :=
  CalleeOk.of_verified hS verified87 (by omega) (by
    have h : (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64).aarch64Depth=0 := by decide
    rw [h]; omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
