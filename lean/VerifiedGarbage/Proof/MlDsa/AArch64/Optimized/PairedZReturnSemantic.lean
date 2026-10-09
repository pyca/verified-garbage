import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZNormComplete
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem zPass_return {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
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
    finishValue (finalPassData false work out aux c d 8).flags=
      if normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j))<B then 1 else 0 := by
  dsimp only
  have hn := zPass_norm_complete (aux:=aux) c hlower hwidth hB hB' hc hs ho hp hy count
  dsimp only at hn
  rw [finishValue_accept _ (finalPass_masks _ _ _ _ _ _ _ (by intro e he; left; simp [vword])),
    hn]
  split <;> simp_all only

end VG.Proof.MlDsa.AArch64.Optimized.Paired
