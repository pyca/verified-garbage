import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHCountPass

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hPass_count_complete {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,0⟩
    sumN 4 (fun e => (vword (finalPassData true work out aux c d 8).count e).toNat)=
      hintOnes ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j) := by
  dsimp only
  rw [hintOnes_pair_sum,←pairedHintSum_order]
  unfold sumN at *
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have he' := List.mem_range.mp he
  rw [finalPass_count work out aux c _ (by decide : 8≤8) ho hd he']
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  rw [hz]
  change (0+(passHintSum work out aux c (firstPassMem m work challenge secret 8) e 8)).toNat=_
  have hv := passHintSum_field (n:=8) (by decide : 8≤8) he' hg c (hgamma e he') hc hs ho ha hd hp hy
  have hzadd := congrArg BitVec.toNat (BitVec.zero_add (passHintSum work out aux c (firstPassMem m work challenge secret 8) e 8))
  exact hzadd.trans hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired
