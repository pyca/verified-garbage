module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdCall
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Private intermediates and status slots survive the check's calls -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def innerSlice (g : PrivGeometry) (d n : Nat) : Region := ⟨off (State.addr g.stack) d, n⟩

theorem innerSlice_sub {g : PrivGeometry} (h : g.Valid) {d n : Nat} (fit : d + n ≤ frameBytes) :
    (innerSlice g d n).Sub g.wholeStack := fun x hx => h.innerSub x (Offset.sub_base _ fit x hx)

theorem innerSlice_external {g : PrivGeometry} (h : g.Valid) {d n : Nat} (fit : d + n ≤ frameBytes) :
    (innerSlice g d n).Disjoint g.outputRegion ∧
    (innerSlice g d n).Disjoint g.workspaceRegion ∧
    (innerSlice g d n).Disjoint g.calleeRegion :=
  ⟨h.stackOutput.sub_left (innerSlice_sub h fit), h.stackWorkspace.sub_left (innerSlice_sub h fit),
    (h.calleeInner.sub_right (Offset.sub_base _ fit)).symm⟩

theorem temporary_region {g : PrivGeometry} (h : g.Valid) :
    (⟨State.addr g.temporary, g.length⟩ : Region) = innerSlice g oM g.length := by
  rw [PrivGeometry.temporary, h.offsetAddr (by decide)]; rfl

theorem precomputation_region {g : PrivGeometry} (h : g.Valid) :
    (⟨State.addr g.precomputation, 16 * Spec.Rsa.modulusWords g.length⟩ : Region) =
      innerSlice g oPre (16 * Spec.Rsa.modulusWords g.length) := by
  rw [PrivGeometry.precomputation, h.offsetAddr (by decide)]; rfl

theorem temporary_pcPrefix {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pcPrefixWrites g, (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint r := by
  intro r hr
  rw [temporary_region h]
  simp only [pcPrefixWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  have bound := h.maxLength
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by decide : 8 ≤ oM) (by simp only [oM]; omega)
  · exact Offset.disjoint _ (Or.inr (by decide : oR1 + 4 ≤ oM))
      (by simp only [oM]; omega) (by decide)

theorem temporary_pcCall {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pcWr g ++ [g.calleeRegion], (⟨State.addr g.temporary, g.length⟩ : Region).Disjoint r := by
  have ex := innerSlice_external h (d := oM) (n := g.length)
    (by have := h.maxLength; simp only [oM, frameBytes]; omega)
  intro r hr
  rw [temporary_region h]
  simp only [pcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [precomputation_region h]
    exact Offset.disjoint _ (Or.inl (by have := h.maxLength; simp only [oM, oPre]; omega))
      (by have := h.maxLength; simp only [oM]; omega)
      (by have := h.maxLength; simp only [oPre, Spec.Rsa.modulusWords]; omega)
  · exact ex.2.1
  · exact ex.2.2

theorem innerSlice_pdCall {g : PrivGeometry} (h : g.Valid) {d n : Nat} (fit : d + n ≤ frameBytes) :
    ∀ r ∈ pdWr g ++ [g.calleeRegion], (innerSlice g d n).Disjoint r := by
  have ex := innerSlice_external h fit
  intro r hr
  simp only [pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ex.1
  · exact ex.2.1
  · exact ex.2.2

theorem innerSlice_pdPrefix {g : PrivGeometry} {d n : Nat} (low : 96 ≤ d) (high : d + n ≤ frameBytes) :
    ∀ r ∈ pdPrefixWrites g, (innerSlice g d n).Disjoint r := by
  intro r hr
  simp only [pdPrefixWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega : 24 ≤ d) (by simp only [frameBytes] at high; omega)
  · exact Offset.disjoint _ (Or.inr (by simp only [oR3]; omega))
      (by simp only [frameBytes] at high; omega) (by decide)
end VG.Proof.Rsa.Arm
