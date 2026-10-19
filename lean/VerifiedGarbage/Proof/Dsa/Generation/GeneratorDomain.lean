module

public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega

/-! # A successful generator search returns a nontrivial residue -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem generator_bounds {p q value : Nat} (hp : 0 < p) (hs : List Nat)
    (h : Spec.Dsa.generator p q hs = some value) : 1 < value ∧ value < p := by
  induction hs with
  | nil => cases h
  | cons x xs ih =>
    rw [generator_cons] at h
    split at h
    · dsimp only at h
      split at h
      · have he : Spec.Dsa.powMod x ((p - 1) / q) p = value := Option.some.inj h
        rw [← he]
        exact ⟨by assumption, VG.Proof.Dsa.powMod_lt _ _ hp⟩
      · exact ih h
    · exact ih h

end VG.Proof.Dsa.Generation
