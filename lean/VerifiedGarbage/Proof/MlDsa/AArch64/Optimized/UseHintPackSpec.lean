import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackFields
import VerifiedGarbage.Proof.MlDsa.Round.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.Spec.MlDsa

theorem fields_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {m : Mem} {h a : Addr} (ha : Reduced m a) :
    fields g m h a = Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
      ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m a) := by
  apply Vector.ext
  intro i hi
  simp only [fields,Vector.getElem_ofFn,Vector.getElem_zipWith]
  rw [value_spec hg (ha i hi)]
  have hpoly : (⟨(coeffAt m a i).toNat,ha i hi⟩ : Zq)=(polyAt m a)[i] :=
    Fin.ext (VG.Proof.MlDsa.Pack.polyAt_val ha hi).symm
  have hh := VG.Proof.MlDsa.Round.hintAt_get m h hi
  rw [VG.Proof.MlDsa.Round.getElem!_eq _ hi] at hh
  rw [hpoly,hh]

theorem packed_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {m : Mem} {h a : Addr} (ha : Reduced m a) :
    packed g m h a = simpleBitPack
      (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
        ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m a)) ((q-1)/(2*g)-1) := by
  rw [packed,fields_spec hg ha]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
