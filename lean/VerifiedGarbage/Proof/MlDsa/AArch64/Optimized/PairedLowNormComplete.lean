import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowAcceptHalves
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLaneNorm
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCoverage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowNormRq

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {g B : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (lowPassData g work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B := by
  dsimp only
  rw [pairedLow_norm_iff _ _ _ _ _ _ (by omega),←lowCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [lowPass_flag_zero_iff _ _ _ _ _ _ (by decide : 8≤8) ho ha hd he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  rw [lowPassAccept,lowPairAccept_halves]
  apply forall_congr'
  intro h
  exact lowLane_norm hu he hg i h c (hscale e he) (hlower e he) (hwidth e he)
    hB hB' hc hs ho.symm hp hy

end VG.Proof.MlDsa.AArch64.Optimized.Paired
