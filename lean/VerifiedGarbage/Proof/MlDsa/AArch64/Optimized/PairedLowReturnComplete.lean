import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowNormComplete
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_return_complete {m : Mem} {work challenge secret out aux : Addr} {g B : Nat}
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
    Response.finishValue (lowPassData g work out aux c d 8).flags =
      if normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B then 1 else 0 := by
  dsimp only
  have hz : FlagMasks (0 : BitVec 128) := by
    intro e he
    exact Or.inl (by simp [vword])
  rw [finishValue_accept _ (lowPass_masks _ _ _ _ _ _ _ hz)]
  have hn := lowPass_norm_complete hg c hscale hlower hwidth hB hB' hc hs ho ha hd hp hy count
  dsimp only at hn
  rw [hn]
  by_cases h : normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
