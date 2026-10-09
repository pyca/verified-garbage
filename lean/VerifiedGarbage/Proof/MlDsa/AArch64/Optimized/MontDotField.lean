import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
import VerifiedGarbage.Spec.MlDsa.MontDot

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

 theorem montCanonical_eq (a : Nat) : ofNat (mont a%q)=ofInt ((mont a:Int)-q) := by
  apply Fin.ext
  simp only [ofNat,Fin.val_ofNat,Nat.mod_mod]
  have h := VG.Proof.MlDsa.KeyGen.ofInt_val ((mont a:Int)-q)
  apply Int.ofNat_inj.mp
  rw [h,Int.natCast_emod]
  change (mont a:Int)%8380417=((mont a:Int)-8380417)%8380417
  omega

def value (s : State) (n : Nat) : Poly :=
  (dotNTT (fun j=>polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j=>polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) n).map (· * montgomeryRInv)

theorem result_field (s : State) {n : Nat} (hn : n≤7) (hp : Pre n s) {i : Nat} (hi : i<256) :
    ofNat (result s n i)=(value s n)[i]! := by
  have ha : ∀j<n,(inputWord s .x1 j i).toNat<3*q := fun j hj=>hp.bound .x1 (by simp) j hj i hi
  have hb : ∀j<n,(inputWord s .x2 j i).toNat<3*q := fun j hj=>hp.bound .x2 (by simp) j hj i hi
  have hf := centeredDot_field (fun j=>inputWord s .x1 j i) (fun j=>inputWord s .x2 j i)
    (fun j=>polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j=>polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) hn ha hb hi
    (fun j _=>by rw [ofInt_nat_eq];exact (polyAt_get _ _ hi).symm)
    (fun j _=>by rw [ofInt_nat_eq];exact (polyAt_get _ _ hi).symm)
  rw [centeredDot_int _ _ hn ha hb] at hf
  rw [result,montCanonical_eq]
  exact hf

theorem result_value (s : State) {n : Nat} (hn : n≤7) (hp : Pre n s) {i : Nat} (hi : i<256) :
    result s n i=((value s n)[i]!).val := by
  have h := congrArg Fin.val (result_field s hn hp hi)
  rw [ofNat,Fin.val_ofNat,Nat.mod_eq_of_lt (show result s n i<q from Nat.mod_lt _ (by decide))] at h
  exact h

theorem output_ok {s₀ s : State} {n : Nat} (hn : n≤7) (hp : Pre n s₀)
    (h : Inv s₀ (result s₀ n) 64 s) : PolyIs s.mem (s₀.gpr .x0) (value s₀ n) := by
  apply polyIs_of_toNat
  intro i hi
  rw [h.coeff i hi,ite_eq_left (by change i<256;exact hi)]
  exact result_value s₀ hn hp hi

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
