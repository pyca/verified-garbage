import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCoordinates
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZFieldValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZUnused
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem firstPass_checkInput_read {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : Fin 2 × Fin 8)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    (firstPassMem m work challenge secret 8).read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16=
      m.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16 := by
  exact (firstPass_frame (m:=m) (a:=challenge) (b:=secret) (by decide : 8≤8)).read
    (checkAddr_contains out hu i)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem zPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let x := coeffAt (finalPassData false work out aux c d 8).mem
      (pairPolyPtr out i.1.val) (4*u+32*i.2.val+e);
    -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
      ofInt x.toInt=(add (polyAt m (pairPolyPtr out i.1.val))
        (pairedProduct m challenge secret i.1.val))[4*u+32*i.2.val+e]! := by
  dsimp only
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  rw [←checkAddr_coeff _ out u i he,
    finalPass_z_read_written work out aux c _ (by decide : 8≤8) hu i ho]
  have hv := zOutput_field c he (raw := (Inverse.rawFinalValues
    (readPair (firstPassMem m work challenge secret 8) (work+BitVec.ofNat 64 (16*u)) 128 i.1))[i.2.val])
    (high := 0)
    (low := (firstPassMem m work challenge secret 8).read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16)
    (by rw [firstPass_checkInput_read hu i ho.symm,checkAddr_coeff _ _ _ _ he]; exact hy _ i.1.isLt _ hk)
    ⟨hr.1,hr.2.1⟩
  refine ⟨hv.1,hv.2.1,hv.2.2.trans ?_⟩
  rw [firstPass_checkInput_read hu i ho.symm,checkAddr_coeff _ _ _ _ he,
    ofInt_add,ofInt_nat_eq,←polyAt_get _ _ hk,hr.2.2,add_get _ _ hk]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
