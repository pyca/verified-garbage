import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskSemantic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem zLane_norm {m : Mem} {work challenge secret out : Addr} {u e B : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    passMask false work out c (firstPassMem m work challenge secret 8) u i e=0 ↔
      normZq (add (polyAt m (pairPolyPtr out i.1.val))
        (pairedProduct m challenge secret i.1.val))[4*u+32*i.2.val+e]!<B := by
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  simp only [passMask,checkMask,Bool.false_eq_true,ite_false,hlower,hwidth]
  rw [firstPass_checkInput_read hu i ho,checkAddr_coeff _ _ _ _ he,
    zMask_zero (hy _ i.1.isLt _ hk) ⟨hr.1,hr.2.1⟩ hB hB',
    ofInt_add,ofInt_nat_eq,←polyAt_get _ _ hk,hr.2.2,add_get _ _ hk]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
