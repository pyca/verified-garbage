module

public import VerifiedGarbage.Proof.Rsa.X86.PrivCheckRegions
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # Saved return bits and private buffers survive the subsequent calls -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem status_pcCall {g : PrivGeometry} (h : g.Valid) {d : Nat} (low : 24 ≤ d) (fit : d + 4 ≤ 88) :
    ∀ r ∈ pcWr g ++ [g.calleeRegion], (innerSlice g d 4).Disjoint r := by
  have ex := innerSlice_external h (d := d) (n := 4)
    (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  intro r hr
  simp only [pcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [precomputation_region h]
    exact Offset.disjoint _ (Or.inl (by simp only [precomputeOffset]; omega)) (by omega)
      (by have := h.maxLength; simp only [precomputeOffset, Spec.Rsa.modulusWords]; omega)
  · exact ex.2.1
  · exact Offset.disjoint_base _ low (by omega)
  · exact ex.2.2

theorem status_frame {g : PrivGeometry} {d : Nat} {regions : List Region} {m m' : Mem}
    (frame : Frame regions m m') (sep : ∀ r ∈ regions, (innerSlice g d 4).Disjoint r) :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 = m.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 :=
  frame.readW (r := innerSlice g d 4) (Region.contains_self _ _) sep (by decide)

theorem temporary_setup {g : PrivGeometry} (h : g.Valid) :
    ∀ (r : Region), r ∈ [⟨byteAddr g.stack, 88⟩] → (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint r := by
  rw [temporary_region h]
  exact innerSlice_setup (by decide : 88 ≤ candidateOffset)
    (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)

theorem precomputation_setup {g : PrivGeometry} (h : g.Valid) :
    ∀ (r : Region), r ∈ [⟨byteAddr g.stack, 88⟩] →
      (⟨byteAddr g.precomputation, 8 * (2 * Spec.Rsa.modulusWords g.length)⟩ : Region).Disjoint r := by
  rw [show 8 * (2 * Spec.Rsa.modulusWords g.length) = 16 * Spec.Rsa.modulusWords g.length by omega,
    precomputation_region h]
  exact innerSlice_setup (by decide : 88 ≤ precomputeOffset)
    (by have := h.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega)

theorem setupWrites_sub {g : PrivGeometry} :
    ∀ (r : Region), r ∈ [⟨byteAddr g.stack, 88⟩] → ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 88 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩

theorem calleeWrites_sub {g : PrivGeometry} {rs : List Region}
    (sub : ∀ r ∈ rs, ∃ R ∈ bodyWrites g, r.Sub R) :
    ∀ r ∈ rs ++ [g.calleeRegion], ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact sub r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩

theorem tailWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ (r : Region), r ∈ [⟨byteAddr g.output, g.length⟩, ⟨byteAddr g.temporary, g.length⟩] → ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)

end VG.Proof.Rsa.X86.PrivChecked
