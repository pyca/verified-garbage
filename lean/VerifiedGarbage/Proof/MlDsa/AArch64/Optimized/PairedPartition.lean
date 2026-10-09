import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHint

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem zCheck_eq (g p j : Nat) : check .z g p j=zLane (vr (8*p+j)) (1024*p+128*j) := rfl

theorem hCheck_eq (g p j : Nat) : check .h g p j=hintLane (vr (8*p+j)) (1024*p+128*j) := rfl

theorem finalPrefix_eq : finalBody.take (finalBody.length-finalStore.length-2)=finalLoads++finalArithmetic := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Paired
