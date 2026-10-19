module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Field
import VerifiedGarbage.Proof.MlKem.Arith

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.Spec.MlKem VG.Proof.MlKem

def gammaValues (i : Nat) : Nat := (gamma i).val

theorem zero_pair {i : Nat} (hi : i < 128) : PairRel (zeroSums 0) zero i := by
  constructor
  · rw [zero_get (by change 2*i<256; omega)]
    simp only [zeroSums,Nat.zero_mul,Nat.add_zero,Nat.zero_mod,val_zero]
  · rw [zero_get (by change 2*i+1<256; omega)]; rfl

theorem result_field (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly)
    {j : Nat} (hj : j < 256) :
    result terms (polyValues F) (polyValues G) gammaValues j =
      BitVec.ofNat 32 ((polySum terms F G)[j]!).val := by
  have hc : j/8 < 32 := by omega
  have he : j%8/2 < 4 := by omega
  have hh := sumTerms_field terms F G hc he (a := zeroSums) (P := zero)
    (zero_pair (i := 4*(j/8)+j%8/2) (by omega))
  unfold result interleave
  split <;> rename_i hp
  · have ji : j = 2*(4*(j/8)+j%8/2) := by omega
    change BitVec.ofNat 32 (((sumTerms terms (blockValues (polyValues F) (j/8))
      (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).even +
      (sumTerms terms (blockValues (polyValues F) (j/8)) (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).odd *
      (gamma (4*(j/8)+j%8/2)).val)%q) = _
    rw [hh.1,←ji]
  · have ji : j = 2*(4*(j/8)+j%8/2)+1 := by omega
    change BitVec.ofNat 32 ((sumTerms terms (blockValues (polyValues F) (j/8))
      (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).cross%q) = _
    rw [hh.2,←ji]

end VG.Proof.MlKem.AArch64.Dot
