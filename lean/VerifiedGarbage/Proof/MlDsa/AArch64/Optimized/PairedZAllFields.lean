import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem zPass_all_fields {m : Mem} {work challenge secret out aux : Addr} (c : CheckConstants)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (finalPassData false work out aux c d 8).mem
    ∀j<2,CenteredReduced result (pairPolyPtr out j) ∧
      signedPolyAt result (pairPolyPtr out j)=add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j) := by
  dsimp only
  intro j hj
  have hv : ∀k<n,
      let x := coeffAt (finalPassData false work out aux c
        ⟨firstPassMem m work challenge secret 8,flags,count⟩ 8).mem (pairPolyPtr out j) k;
      -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
        ofInt x.toInt=(add (polyAt m (pairPolyPtr out j)) (pairedProduct m challenge secret j))[k]! := by
    intro k hk
    obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
    have h := zPass_stored_field (aux:=aux) hu he (⟨j,hj⟩,⟨k/32,hi⟩) c hc hs ho hp hy flags count
    simpa only [←heq] using h
  constructor
  · intro k hk
    have h := hv k hk
    change -8380417<_ ∧ _<8380417
    exact ⟨by omega,by omega⟩
  · apply Vector.ext
    intro k hk
    simpa only [signedPolyAt,Vector.getElem_ofFn,VG.Proof.MlDsa.Arith.getElem!_eq _ hk] using (hv k hk).2.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired
