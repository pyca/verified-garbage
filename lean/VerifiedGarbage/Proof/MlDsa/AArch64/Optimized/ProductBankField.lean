import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

def productBankValues (s : State) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => ofVWords
    (productInput s (16*j.val) 0) (productInput s (16*j.val) 1)
    (productInput s (16*j.val) 2) (productInput s (16*j.val) 3)

theorem productBankValues_word (s : State) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (productBankValues s)[j.val] e=productInput s (16*j.val) e := by
  simp only [productBankValues,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Shifted input pointers select the corresponding global coefficient. -/
theorem productInput_offset {s : State} {a b : Addr} {u j e : Nat}
    (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u)) (he : e<4) :
    productInput s (16*j) e=centeredProduct
      (coeffAt s.mem a (32*u+4*j+e)) (coeffAt s.mem b (32*u+4*j+e)) := by
  unfold productInput
  rw [ha,hb,vword_read16 _ _ he,vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add]
  congr 3 <;> congr 1 <;> omega

/-- Each resident bank starts the inverse within its q bound, even though
its forward-transform inputs are positive representatives below 3q. -/
theorem productBankValues_bound {s : State} {a b : Addr} {f g : Poly} {u : Nat}
    (hu : u<8) (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u))
    (hf : PosPolyIs s.mem a f) (hg : PosPolyIs s.mem b g)
    (j : Fin 8) {e : Nat} (he : e<4) :
    -(q : Int)≤(vword (productBankValues s)[j.val] e).toInt ∧
      (vword (productBankValues s)[j.val] e).toInt≤(q : Int) := by
  rw [productBankValues_word s j he,productInput_offset ha hb he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  have hx := centeredProduct_bounds _ _ (hf.bound _ hk) (hg.bound _ hk)
  constructor
  · exact hx.1
  · have hq : (q : Int)=8380417 := rfl; omega

theorem productBankValues_field {s : State} {a b : Addr} {f g : Poly} {u : Nat}
    (hu : u<8) (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u))
    (hf : PosPolyIs s.mem a f) (hg : PosPolyIs s.mem b g)
    (j : Fin 8) {e : Nat} (he : e<4) :
    ofInt (vword (productBankValues s)[j.val] e).toInt =
      (Representation.product true f g)[32*u+4*j.val+e]! := by
  rw [productBankValues_word s j he,productInput_offset ha hb he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  have hs := centeredProduct_scaled _ _ (hf.bound _ hk) (hg.bound _ hk)
  rw [ofInt_nat_eq,ofInt_nat_eq,← polyAt_get _ _ hk,← polyAt_get _ _ hk,hf.value,hg.value] at hs
  have heq := congrArg (fun x : Zq => x*montgomeryRInv) hs
  have hc : ofInt 4294967296*montgomeryRInv=1 := by decide +kernel
  rw [Fin.mul_assoc,hc,Fin.mul_one] at heq
  change _ = (Montgomery.scale montgomeryRInv (multiplyNTT f g))[_]!
  rw [Montgomery.scale_get,mul_get _ _ hk]
  exact heq

end VG.Proof.MlDsa.AArch64.Optimized
