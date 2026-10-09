import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductPassMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankField

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem productValues_bound {m : Mem} {a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) {u : Nat} (hu : u<8) :
    BankBound (productValues m a b u) 8380417 := by
  intro j e he
  rw [productValues_word _ _ _ _ _ he]
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  have h := centeredProduct_bounds _ _ (hf.bound _ hi) (hg.bound _ hi)
  change -8380417≤_ ∧ _≤8380417
  change -8380417≤_ ∧ _≤147168 at h
  omega

theorem productValues_field {m : Mem} {a b : Addr} {f g : Poly}
    (hf : PosPolyIs m a f) (hg : PosPolyIs m b g) {u : Nat} (hu : u<8) :
    InnerBankField u (productValues m a b u) (Representation.product true f g) := by
  intro j e he
  rw [productValues_word _ _ _ _ _ he]
  have hi : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  have hs := centeredProduct_scaled _ _ (hf.bound _ hi) (hg.bound _ hi)
  rw [ofInt_nat_eq,ofInt_nat_eq,← polyAt_get _ _ hi,← polyAt_get _ _ hi,hf.value,hg.value] at hs
  have hc : ofInt 4294967296 * montgomeryRInv = 1 := by decide +kernel
  have hv := congrArg (fun x : Zq => x * montgomeryRInv) hs
  rw [Fin.mul_assoc,hc,Fin.mul_one] at hv
  change _ = (Montgomery.scale montgomeryRInv (multiplyNTT f g))[32*u+4*j.val+e]!
  rw [Montgomery.scale_get,mul_get _ _ hi]
  exact hv

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
