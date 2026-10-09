import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16)

/-- Reading one register lane is reading its original polynomial coefficient. -/
theorem readBank_coeff (m : Mem) (p : Addr) (start step : Nat) (i : Fin 8)
    {e : Nat} (he : e<4) :
    vword (readBank m (coeffAddr p start) (4*step))[i.val] e =
      coeffAt m p (start+step*i.val+e) := by
  simp only [readBank,Vector.getElem_ofFn]
  rw [show 4*step*i.val=4*(step*i.val) from Nat.mul_assoc _ _ _,coeffAddr_add,vword_read16 _ _ he,coeffAddr_add]
  rfl

/-- Each store changes precisely four coefficients. -/
theorem writeBank_coeff_fold (v : Vector (BitVec 128) 8) (m : Mem) (p : Addr)
    {start step k : Nat} (hb : start+step*7+4≤256) (hk : k<256) :
    coeffAt (writeBank v (coeffAddr p start) (4*step) m) p k =
      (List.finRange 8).foldl (fun w i =>
        if start+step*i.val≤k ∧ k<start+step*i.val+4 then
          vword v[i.val] (k-(start+step*i.val)) else w) (coeffAt m p k) := by
  have go (is : List (Fin 8)) (m : Mem) :
      coeffAt (is.foldl (fun m i => m.write
        (coeffAddr p start+BitVec.ofNat 64 (4*step*i.val)) 16 v[i.val]) m) p k =
      is.foldl (fun w i => if start+step*i.val≤k ∧ k<start+step*i.val+4 then
        vword v[i.val] (k-(start+step*i.val)) else w) (coeffAt m p k) := by
    induction is generalizing m with
    | nil => rfl
    | cons i is ih =>
      simp only [List.foldl_cons]
      rw [ih,show 4*step*i.val=4*(step*i.val) from Nat.mul_assoc _ _ _,coeffAddr_add,
        coeffAt_write16 _ _ (by
          have h := Nat.mul_le_mul_left step (show i.val≤7 by omega)
          omega) _ hk]
  exact go _ m

/-- Repeated overwrites of a single selected slot have the expected result. -/
theorem fold_select {α β : Type} [DecidableEq α] (xs : List α) (selected : α) (v w : β) :
    xs.foldl (fun w i => if i=selected then v else w) w = if selected∈xs then v else w := by
  induction xs generalizing w with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons,ih,List.mem_cons]
    by_cases h : i=selected
    · subst i; simp
    · by_cases hx : selected∈xs <;> simp [h,Ne.symm h,hx]

/-- A bank store writes the selected lane even when the base wraps modulo 2^64. -/
theorem writeBank_coeff_at (v : Vector (BitVec 128) 8) (m : Mem) (p : Addr)
    {start step : Nat} (hs : 4≤step) (hb : start+step*7+4≤256)
    (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (writeBank v (coeffAddr p start) (4*step) m) p (start+step*i.val+e)=vword v[i.val] e := by
  have hi := Nat.mul_le_mul_left step (show i.val≤7 by omega)
  rw [writeBank_coeff_fold v m p hb (by omega)]
  have ef : (fun (w : BitVec 32) (j : Fin 8) =>
      if start+step*j.val≤start+step*i.val+e ∧ start+step*i.val+e<start+step*j.val+4 then
        vword v[j.val] (start+step*i.val+e-(start+step*j.val)) else w) =
      (fun w j => if j=i then vword v[i.val] e else w) := by
    funext w j
    by_cases h : j=i
    · subst j; simp [he]
    · have hj : j.val≠i.val := fun hv => h (Fin.ext hv)
      have hd : step*j.val+4≤step*i.val ∨ step*i.val+4≤step*j.val := by
        rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · left; have := Nat.mul_le_mul_left step (show j.val+1≤i.val by omega)
          rw [Nat.mul_add,Nat.mul_one] at this; omega
        · right; have := Nat.mul_le_mul_left step (show i.val+1≤j.val by omega)
          rw [Nat.mul_add,Nat.mul_one] at this; omega
      have hn : ¬(start+step*j.val≤start+step*i.val+e ∧ start+step*i.val+e<start+step*j.val+4) := by omega
      simp only [hn,h,ite_false]
  rw [ef,fold_select]
  simp

/-- Coefficients outside all eight stores are untouched. -/
theorem writeBank_coeff_outside (v : Vector (BitVec 128) 8) (m : Mem) (p : Addr)
    {start step k : Nat} (hb : start+step*7+4≤256) (hk : k<256)
    (hout : ∀ i : Fin 8, ¬(start+step*i.val≤k ∧ k<start+step*i.val+4)) :
    coeffAt (writeBank v (coeffAddr p start) (4*step) m) p k=coeffAt m p k := by
  rw [writeBank_coeff_fold v m p hb hk]
  have hf : (fun (w : BitVec 32) (i : Fin 8) =>
      if start+step*i.val≤k ∧ k<start+step*i.val+4 then
        vword v[i.val] (k-(start+step*i.val)) else w) = (fun w _ => w) := by
    funext w i
    exact ite_eq_right (hout i)
  rw [hf]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized
