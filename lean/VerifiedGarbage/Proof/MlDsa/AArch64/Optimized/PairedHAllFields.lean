import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHStoredField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hPass_all_fields {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    HintIs (finalPassData true work out aux c d 8).mem out 2
      ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j) := by
  dsimp only
  refine ⟨by simp,?_⟩
  intro j hj k hk
  obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
  have hv := hPass_stored_field hu he hg (⟨j,hj⟩,⟨k/32,hi⟩) c (hgamma _ he)
    hc hs ho ha hd hp hy flags count
  have hv' : coeffAt (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,flags,count⟩ 8).mem (pairPolyPtr out j) k=
      BitVec.ofNat 32 (pairedHintPoly m challenge secret out aux g j)[k]!.toNat := by
    simpa only [←heq] using hv
  have hpointer : ∀mm:Mem,coeffAt mm out (256*j+k)=coeffAt mm (pairPolyPtr out j) k := by
    intro mm
    simp only [coeffAt,pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 4*(256*j+k)=1024*j+4*k by omega]
  rw [hpointer,hv']
  have hj' : j<((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j).length := by simpa using hj
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some,
    List.getElem_map,List.getElem_range]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
