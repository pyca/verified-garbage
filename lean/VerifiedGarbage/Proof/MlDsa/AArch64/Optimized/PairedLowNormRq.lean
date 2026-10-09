import VerifiedGarbage.Spec.MlDsa.PairedResponse
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.Arith.Zq

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The shared paired norm is exactly the strict low-bits check on all coefficients. -/
theorem pairedLow_norm_iff (m : Mem) (challenge secret out : Addr) (g B : Nat) (hB : 0<B) :
    normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B ↔
      ∀j<2,∀k<n,normZq (ofInt (lowBits g (pairedDifference m challenge secret out j)[k]!))<B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp only [List.forall_mem_map,List.mem_range]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  rw [VG.Proof.MlDsa.Round.normRq_lt]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  rw [pairedLowPoly,getElem!_eq _ hk,Vector.getElem_map,getElem!_eq _ hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
