import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintSpec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem hPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    coeffAt (finalPassData true work out aux c d 8).mem
      (pairPolyPtr out i.1.val) (4*u+32*i.2.val+e)=
      BitVec.ofNat 32 (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat := by
  dsimp only
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  rw [←checkAddr_coeff _ out u i he,
    finalPass_read_written true work out aux c _ (by decide : 8≤8) hu i ho hd]
  simp only [checkOutput,ite_true,laneVector_word _ he]
  rw [firstPass_checkInput_read hu i ho.symm,firstPass_checkInput_read hu i ha.symm,
    checkAddr_coeff _ _ _ _ he,checkAddr_coeff _ _ _ _ he,hgamma]
  have hpj := hy i.1.val i.1.isLt _ hk
  have hhigh : (coeffAt m (pairPolyPtr aux i.1.val) (4*u+32*i.2.val+e)).toInt=
      highBits g (responseHintBase m (pairPolyPtr out i.1.val) (pairPolyPtr aux i.1.val) g (4*u+32*i.2.val+e)) := by
    have hb := highBits_small hg (responseHintBase m (pairPolyPtr out i.1.val) (pairPolyPtr aux i.1.val) g (4*u+32*i.2.val+e))
    have hi := BitVec.toInt_eq_toNat_cond (coeffAt m (pairPolyPtr aux i.1.val) (4*u+32*i.2.val+e))
    omega
  rw [hintWord_raw_field hg _ _ _ _ hr.1 hr.2.1 hpj.1 hhigh,hr.2.2,
    getElem!_pos (pairedHintPoly m challenge secret out aux g i.1.val) (4*u+32*i.2.val+e) hk]
  simp only [pairedHintPoly,Vector.getElem_ofFn]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
