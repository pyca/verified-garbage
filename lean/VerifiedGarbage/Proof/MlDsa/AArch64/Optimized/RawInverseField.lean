import VerifiedGarbage.Spec.MlDsa.RawInverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem signedPolyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i<n) :
    (signedPolyAt m p)[i]! =ofInt (coeffAt m p i).toInt := by
  rw [_root_.getElem!_pos (signedPolyAt m p) i hi]
  simp only [signedPolyAt,Vector.getElem_ofFn]

/-- Caller-facing form of the raw contract: strict bounds and exact field
values, without interpreting a negative coefficient as an unsigned integer. -/
theorem rawPolyIs_iff {m : Mem} {p : Addr} {f : Poly} :
    RawPolyIs m p f ↔ ∀ i<n,
      -(q : Int)<(coeffAt m p i).toInt ∧ (coeffAt m p i).toInt<2*(q : Int) ∧
      ofInt (coeffAt m p i).toInt=f[i]! := by
  constructor
  · rintro ⟨hb,hf⟩ i hi
    exact ⟨(hb i hi).1,(hb i hi).2,by rw [← signedPolyAt_get m p hi,hf]⟩
  · intro h
    refine ⟨fun i hi => ⟨(h i hi).1,(h i hi).2.1⟩,ext_getElem! fun i hi => ?_⟩
    rw [signedPolyAt_get m p hi]
    exact (h i hi).2.2

end VG.Proof.MlDsa.AArch64.Optimized
