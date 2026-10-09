import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHOutputField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintOrder
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCountBound

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hintSum_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let mem := firstPassMem m work challenge secret 8
    (hintSum (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p))
      (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c mem e allChecks).toNat=
      sumN 2 (fun p => sumN 8 (fun j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat)) := by
  dsimp only
  unfold hintSum
  rw [(bitSum_value _ (by rw [List.length_map]; decide)
    (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact checkOutput_bit _ _ _ _ he)).1]
  simp only [List.map_map,Function.comp_def]
  have hm := List.map_congr_left (l:=allChecks) (fun i _ =>
    hOutput_field hu he hg i c hgamma hc hs ho ha hd hp hy)
  rw [hm]
  exact allChecks_sum (fun p j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
