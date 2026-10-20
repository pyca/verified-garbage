module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Retain the callee return bits and precomputation across subsequent setup -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem status_pcCall {g : PrivGeometry} (h : g.Valid) {d : Nat} (fit : d + 4 ≤ 96) :
    ∀ r ∈ pcWr g ++ [g.calleeRegion], (innerSlice g d 4).Disjoint r := by
  have ex := innerSlice_external h (d := d) (n := 4) (by simp only [frameBytes]; omega)
  intro r hr
  simp only [pcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [precomputation_region h]
    exact Offset.disjoint _ (Or.inl (by simp only [oPre]; omega)) (by omega)
      (by have := h.maxLength; simp only [oPre, Spec.Rsa.modulusWords]; omega)
  · exact ex.2.1
  · exact ex.2.2

theorem statusR1_pdPrefix (g : PrivGeometry) :
    ∀ r ∈ pdPrefixWrites g, (innerSlice g oR1 4).Disjoint r := by
  intro r hr
  simp only [pdPrefixWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by decide : 24 ≤ oR1) (by decide)
  · exact Offset.disjoint _ (Or.inl (by decide : oR1 + 4 ≤ oR3)) (by decide) (by decide)

theorem status_frame {g : PrivGeometry} {d : Nat} {regions : List Region} {m m' : Mem}
    (frame : Frame regions m m') (sep : ∀ r ∈ regions, (innerSlice g d 4).Disjoint r) :
    m'.readW (off (State.addr g.stack) d) 32 = m.readW (off (State.addr g.stack) d) 32 :=
  frame.readW (r := innerSlice g d 4) (Region.contains_self _ _) sep (by decide)

theorem precomputation_pdPrefix {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pdPrefixWrites g, (⟨State.addr g.precomputation, 8 * (2 * Spec.Rsa.modulusWords g.length)⟩ : Region).Disjoint r := by
  rw [show 8 * (2 * Spec.Rsa.modulusWords g.length) = 16 * Spec.Rsa.modulusWords g.length by omega,
    precomputation_region h]
  exact innerSlice_pdPrefix (by decide : 96 ≤ oPre)
    (by have := h.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega)

theorem wordsAt_frame {regions : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (frame : Frame regions m m') (fit : 8 * n < 2 ^ 64)
    (sep : ∀ r ∈ regions, (⟨p, 8 * n⟩ : Region).Disjoint r) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n :=
  VG.Proof.Rsa.wordsAt_frame frame fit sep

end VG.Proof.Rsa.Arm
