module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicCall

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
