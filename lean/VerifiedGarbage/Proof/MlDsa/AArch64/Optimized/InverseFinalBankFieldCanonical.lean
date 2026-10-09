import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa

/-- The final store's existing correction preserves each field value and
produces its canonical representative, given the strict Barrett range. -/
theorem canonicalValues_lane (v : Vector (BitVec 128) 8) (qv : BitVec 128)
    (i : Fin 8) {e : Nat} (he : e<4) (hq : vword qv e=8380417#32)
    (hl : -8380417<(vword v[i.val] e).toInt)
    (hh : (vword v[i.val] e).toInt<2*8380417) :
    (vword (canonicalValues v qv)[i.val] e).toNat<8380417 ∧
      ofInt (vword (canonicalValues v qv)[i.val] e).toInt=ofInt (vword v[i.val] e).toInt := by
  simp only [canonicalValues,Vector.getElem_ofFn]
  rw [canonicalVector_word _ _ he hq]
  exact ⟨canonicalWord_bounds _ hl hh,canonicalWord_field _ hl hh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
