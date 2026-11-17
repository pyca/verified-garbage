module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

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
  exact frame.bytes (R := ⟨src, k⟩) sep (by change k ≤ 2 ^ 64; omega_using [fit]) (List.mem_range.mp hj)


theorem wordsAt_frame {regions : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (frame : Frame regions m m') (fit : 8 * n < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨p, 8 * n⟩ : Region).Disjoint r) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact frame.readW (r := ⟨p, 8 * n⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [fit, hi])) sep (by decide)

/-- `Spec.Rsa.written` of a buffer apart from a frame, whatever the frame's
bytes hold. -/
theorem written_frame {regions : List Region} {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32}
    {o : Option (List Byte)} (frame : Frame regions m m') (fit : n < 2 ^ 64)
    (sep : ∀ q ∈ regions, (⟨out, n⟩ : Region).Disjoint q) (h : Spec.Rsa.written m out n r o) :
    Spec.Rsa.written m' out n r o := by
  have hb := rsa_bytes_frame frame fit sep
  cases o <;> simp only [Spec.Rsa.written] at h ⊢ <;> rw [hb] <;> exact h

/-- `Spec.Rsa.writtenOutcome` of a buffer apart from a frame, whatever the
frame's bytes hold. -/
theorem writtenOutcome_frame {regions : List Region} {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32}
    {o : Spec.Rsa.Outcome} (frame : Frame regions m m') (fit : n < 2 ^ 64)
    (sep : ∀ q ∈ regions, (⟨out, n⟩ : Region).Disjoint q) (h : Spec.Rsa.writtenOutcome m out n r o) :
    Spec.Rsa.writtenOutcome m' out n r o := by
  have hb := rsa_bytes_frame frame fit sep
  cases o <;> simp only [Spec.Rsa.writtenOutcome] at h ⊢ <;> rw [hb] <;> exact h

end VG.Proof.Rsa
