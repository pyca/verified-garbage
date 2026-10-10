import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCoordinates
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawField

/-! ## From `PairedZUnused.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The z check does not read or depend on its auxiliary argument. -/
theorem checkStep_z_aux (raw : BitVec 128) (out aux aux' : Addr)
    (c : CheckConstants) (d : CheckData) :
    checkStep false raw out aux c d=checkStep false raw out aux' c d := by
  simp only [checkStep,Bool.false_eq_true,ite_false]

theorem checkRun_z_aux (v : Values) (out aux aux' : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) :
    checkRun false v out aux c d js=checkRun false v out aux' c d js := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    simp only [checkRun]
    rw [checkStep_z_aux _ _ _ (aux'+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)),ih]

theorem finalPass_z_aux (work out aux aux' : Addr) (c : CheckConstants)
    (d : CheckData) (n : Nat) :
    finalPassData false work out aux c d n=finalPassData false work out aux' c d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finalPassData,ih]
    exact checkRun_z_aux _ _ _ _ _ _ _

/-- Exact z output with an arbitrary unused auxiliary argument. -/
theorem finalPass_z_read_written (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : Fin 2 × Fin 8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData false work out aux c d n).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      checkOutput false ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
        (d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16) 0 c := by
  rw [finalPass_z_aux work out aux work]
  have h := finalPass_read_written false work out work c d hn hk i hw hw
  simpa only [checkOutput,Bool.false_eq_true,ite_false] using h

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZFieldValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- The fused z store is the same centered representative on successful and
unsuccessful attempts. -/
theorem zOutput_field {raw low high : BitVec 128} (c : CheckConstants)
    {e : Nat} (he : e<4) (hl : (vword low e).toNat<8380417)
    (hr : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    let x := vword (checkOutput false raw low high c) e;
    -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
      ofInt x.toInt=ofInt ((vword low e).toNat+(vword raw e).toInt) := by
  simp only [checkOutput,laneVector_word _ he,Bool.false_eq_true,ite_false]
  rw [BitVec.add_comm (vword raw e),addReduced_int _ _ hl hr]
  have hb := reduce32_bounds (by omega : -2*8380417<(vword low e).toNat+(vword raw e).toInt)
    (by omega : (vword low e).toNat+(vword raw e).toInt<3*8380417)
  exact ⟨hb.1,hb.2,reduce32_field _⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZStoredField.lean` -/

section

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

end
