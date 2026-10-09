import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

theorem positiveWord_field (x : BitVec 32) :
    ofNat (positiveWord x).toNat = ofInt x.toInt := by
  have hp := positive_bounds (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [val_ofNat, Int.natCast_emod, positiveWord_nat,
    Int.toNat_of_nonneg (by omega), VG.Proof.MlDsa.KeyGen.ofInt_val]
  exact positive_mod _

/-- Normalizing signed representatives changes the internal storage relation,
not the polynomial represented by memory. No canonical-output claim is made. -/
theorem SignedPolyIs.positive {m m' : Mem} {p p' : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi)
    (hw : ∀ i < n, coeffAt m' p' i = positiveWord (coeffAt m p i)) :
    PosPolyIs m' p' f := by
  constructor
  · intro i hn
    rw [hw i hn, positiveWord_nat]
    have hp := positive_lt_three_q (BitVec.le_toInt (coeffAt m p i))
      (BitVec.toInt_lt (x := coeffAt m p i))
    omega
  · apply ext_getElem!
    intro i hn
    rw [polyAt_get _ _ hn, hw i hn, positiveWord_field]
    exact h.value i hn

end VG.Proof.MlDsa.AArch64.Optimized
