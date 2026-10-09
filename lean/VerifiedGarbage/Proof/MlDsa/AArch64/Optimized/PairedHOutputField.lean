import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHStoredField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hOutput_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let mem := firstPassMem m work challenge secret 8
    (vword (checkOutput true
      ((Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 i.1))[i.2.val])
      (mem.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16)
      (mem.read (checkAddr (aux+BitVec.ofNat 64 (16*u)) i) 16) c) e).toNat=
      (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat := by
  dsimp only
  have h := hPass_stored_field hu he hg i c hgamma hc hs ho ha hd hp hy 0 0
  dsimp only at h
  rw [←checkAddr_coeff _ out u i he,
    finalPass_read_written true work out aux c _ (by decide : 8≤8) hu i ho hd] at h
  rw [h,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have hb := (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat_le
  omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired
