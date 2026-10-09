import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProductField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryBankField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Each paired input bank is exactly the previously verified product bank. -/
theorem valuesAt_productValues (m : Mem) (a b : Addr) (u : Nat) (poly : Fin 2) :
    valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly =
      Inverse.productValues m a (b+BitVec.ofNat 64 (1024*poly.val)) u := by
  apply Vector.ext
  intro j hj
  apply vec_ext
  intro e he
  exact (valuesAt_coeff m a b u poly ⟨j,hj⟩ he).trans
    (Inverse.productValues_word m a (b+BitVec.ofNat 64 (1024*poly.val)) u ⟨j,hj⟩ he).symm

/-- The paired five-layer transform preserves the exact field meaning and
its signed 32q bound for either polynomial. -/
theorem fiveValues_field {m : Mem} {a b : Addr} {u : Nat} {poly : Fin 2} {f g : Poly}
    (hu : u<8) (hf : PosPolyIs m a f)
    (hg : PosPolyIs m (b+BitVec.ofNat 64 (1024*poly.val)) g) :
    BankBound (Inverse.fiveValues u
      (valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)) 268173344 ∧
    InnerBankField u (Inverse.fiveValues u
      (valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly))
      (InverseTraversal.run (InverseTraversal.localSlice u) (Representation.product true f g)) := by
  rw [valuesAt_productValues]
  exact Inverse.fiveValues_field _ _ hu (Inverse.productValues_bound hf hg hu)
    (Inverse.productValues_field hf hg hu)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
