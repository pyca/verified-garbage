module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputePre
public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicPre

import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
/-! # Saved return bits and private buffers survive the subsequent calls -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/PrivCheckRegions.lean`, which only this module imported.
section

/-! # Private intermediates and status slots survive the check's calls -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

def innerSlice (g : PrivGeometry) (d n : Nat) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 d, n⟩

theorem innerSlice_sub {g : PrivGeometry} (h : g.Valid) {d n : Nat} (fit : d + n ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes) :
    (innerSlice g d n).Sub g.wholeStack := fun x hx => h.innerSub x (Offset.sub_base _ fit x hx)

theorem innerSlice_external {g : PrivGeometry} (h : g.Valid) {d n : Nat} (fit : d + n ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes) :
    (innerSlice g d n).Disjoint g.outputRegion ∧
    (innerSlice g d n).Disjoint g.workspaceRegion ∧
    (innerSlice g d n).Disjoint g.calleeRegion :=
  ⟨h.stackOutput.sub_left (innerSlice_sub h fit), h.stackWorkspace.sub_left (innerSlice_sub h fit),
    (h.calleeInner.sub_right (Offset.sub_base _ fit)).symm⟩

theorem temporary_region {g : PrivGeometry} (h : g.Valid) :
    (⟨byteAddr g.temporary, g.length⟩ : Region) = innerSlice g candidateOffset g.length := by
  rw [PrivGeometry.temporary, h.offsetAddr (by decide)]; rfl

theorem precomputation_region {g : PrivGeometry} (h : g.Valid) :
    (⟨byteAddr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region) =
      innerSlice g precomputeOffset (16 * Spec.Rsa.modulusWords g.length) := by
  rw [PrivGeometry.precomputation, h.offsetAddr (by decide)]; rfl

theorem innerSlice_setup {g : PrivGeometry} {d n : Nat} (low : 88 ≤ d)
    (high : d + n ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes) :
    ∀ r ∈ [⟨byteAddr g.stack, 88⟩], (innerSlice g d n).Disjoint r := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint_base _ low (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes] at high; omega)

theorem temporary_pcCall {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pcWr g ++ [g.calleeRegion], (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint r := by
  have ex := innerSlice_external h (d := candidateOffset) (n := g.length)
    (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  intro r hr
  rw [temporary_region h]
  simp only [pcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [precomputation_region h]
    exact Offset.disjoint _ (Or.inl (by have := h.maxLength; simp only [candidateOffset, precomputeOffset]; omega))
      (by have := h.maxLength; simp only [candidateOffset]; omega)
      (by have := h.maxLength; simp only [precomputeOffset, Spec.Rsa.modulusWords]; omega)
  · exact ex.2.1
  · exact Offset.disjoint_base _ (by decide : 24 ≤ candidateOffset) (by have := h.maxLength; simp only [candidateOffset]; omega)
  · exact ex.2.2

theorem innerSlice_pdCall {g : PrivGeometry} (h : g.Valid) {d n : Nat} (low : 40 ≤ d) (fit : d + n ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes) :
    ∀ r ∈ pdWr g ++ [g.calleeRegion], (innerSlice g d n).Disjoint r := by
  have ex := innerSlice_external h fit
  intro r hr
  simp only [pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ex.1
  · exact ex.2.1
  · exact Offset.disjoint_base _ low (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes] at fit; omega)
  · exact ex.2.2

end VG.Proof.Rsa.X86.PrivChecked
end

end

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
