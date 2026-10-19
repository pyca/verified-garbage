module

public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # RSA input bytes outside a changed region are preserved -/

@[expose] public section
namespace VG.Proof.Rsa
open VG

theorem rsa_bytes_frame {regions : List Region} {m m' : Mem} {src : Addr} {k : Nat}
    (frame : Frame regions m m') (fit : k < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨src, k⟩ : Region).Disjoint r) :
    Spec.Rsa.bytesAt m' src k = Spec.Rsa.bytesAt m src k := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro j hj
  exact frame.bytes (R := ⟨src, k⟩) sep (by change k ≤ 2 ^ 64; omega) (List.mem_range.mp hj)


theorem wordsAt_frame {regions : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (frame : Frame regions m m') (fit : 8 * n < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨p, 8 * n⟩ : Region).Disjoint r) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact frame.readW (r := ⟨p, 8 * n⟩) (Offset.contains_base _ (by omega) (by omega)) sep (by decide)

end VG.Proof.Rsa
