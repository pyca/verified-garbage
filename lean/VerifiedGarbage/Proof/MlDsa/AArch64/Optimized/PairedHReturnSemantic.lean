import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHCountComplete
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHNormComplete
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintFinishSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem hPass_return {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (g-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*g-1))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,0⟩
    let result := finalPassData true work out aux c d 8
    hintFinishValue result.count result.flags=BitVec.ofNat 64
      (hintOnes ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j)+
        if normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<g then 4294967296 else 0) := by
  dsimp only
  have hgb : 1≤g ∧ g≤524288 := by rcases hg with rfl|rfl <;> decide
  have hnorm := hPass_norm_complete (aux:=aux) c hlower hwidth hgb.1 hgb.2 hc hs ho hp 0
  dsimp only at hnorm
  have hfinish : finishValue (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,0,0⟩ 8).flags=
      if normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<g then 1 else 0 := by
    rw [finishValue_accept _ (finalPass_masks _ _ _ _ _ _ _ (by intro e he; left; simp [vword])),hnorm]
    split <;> simp_all only
  have hbound : ∀e<4,(vword (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,0,0⟩ 8).count e).toNat≤128 := by
    intro e he
    rw [finalPass_count work out aux c _ (by decide : 8≤8) ho hd he]
    have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
    rw [hz]
    have hb := passHintSum_bound work out aux c (firstPassMem m work challenge secret 8) he (by decide : 8≤8)
    exact (congrArg BitVec.toNat (BitVec.zero_add _)).trans_le hb
  rw [hintFinish_packed _ _ _ hbound hfinish]
  have hcount := hPass_count_complete hg c hgamma hc hs ho ha hd hp hy 0
  dsimp only at hcount
  rw [hcount]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
