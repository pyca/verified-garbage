import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckCoverage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZLaneNorm

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem zPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (finalPassData false work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j))<B := by
  dsimp only
  rw [paired_norm_iff _ (by omega),←checkCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [finalPass_flag_zero_iff false work out aux c _ (by decide : 8≤8) ho he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  exact zLane_norm hu he i c (hlower e he) (hwidth e he) hB hB' hc hs ho.symm hp hy

end VG.Proof.MlDsa.AArch64.Optimized.Paired
