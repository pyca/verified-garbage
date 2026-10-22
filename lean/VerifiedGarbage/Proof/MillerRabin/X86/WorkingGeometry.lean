module

public import VerifiedGarbage.Proof.MillerRabin.X86.Preservation
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-! # Static and writable portions of the compact primality workspace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt)

def StaticRange (w d n : Nat) : Prop :=
  ∀ r ∈ workingRanges w, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d

theorem working_bounds (w : Nat) : ∀ r ∈ workingRanges w, r.1 + r.2 ≤ arrAt w 28 := by
  intro r hr
  simp only [workingRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [scratch, Spec.Rsa.MontMul.scratchBytes, arrAt, Spec.Rsa.Mont.hdrBytes]
    omega

theorem header_static (w : Nat) {d n : Nat} (h : d + n ≤ 184) : StaticRange w d n := by
  intro r hr
  simp only [workingRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [scratch, arrAt, Spec.Rsa.Mont.hdrBytes]
    omega

theorem array_static {w j : Nat} (hw : 4 ≤ w) (hj : j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
    StaticRange w (arrAt w j) (8 * (w + 2)) := by
  intro r hr
  simp only [workingRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hj with rfl | rfl | rfl | rfl
  all_goals
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [scratch, Spec.Rsa.MontMul.scratchBytes, arrAt, Spec.Rsa.Mont.hdrBytes]
    omega

theorem StaticRange.prefix {w d n k : Nat} (h : StaticRange w d n) (hk : k ≤ n) : StaticRange w d k := by
  intro r hr
  have := h r hr
  omega

theorem StaticRange.subrange {w d n e k : Nat} (h : StaticRange w d n)
    (lo : d ≤ e) (hi : e + k ≤ d + n) : StaticRange w e k := by
  intro r hr
  have := h r hr
  omega

theorem mutable_array {w j : Nat} (hj : j = 5 ∨ j = 6 ∨ j = 8 ∨ (11 ≤ j ∧ j < 27)) (base : Addr) :
    ∃ r ∈ workingRanges w, Region.Sub ⟨off base (arrAt w j), 8 * w⟩ ⟨off base r.1, r.2⟩ := by
  rcases hj with rfl | rfl | rfl | ⟨lo, hi⟩
  · exact ⟨(arrAt w 5, 8 * w), by simp [workingRanges], fun _ h => h⟩
  · exact ⟨(arrAt w 6, 8 * w), by simp [workingRanges], fun _ h => h⟩
  · exact ⟨(arrAt w 8, 8 * w), by simp [workingRanges], fun _ h => h⟩
  · refine ⟨(arrAt w 11, 16 * (8 * (w + 2))), by simp [workingRanges], ?_⟩
    apply Offset.sub _ (array_monotone w lo)
    have h := array_monotone w (show j + 1 ≤ 27 by omega)
    simp only [arrAt, Nat.add_mul, Nat.one_mul] at h ⊢
    omega

theorem mutable_header {w d : Nat} (hd : d ∈ [184, 188, 212, 232, 236, 240, 244]) (base : Addr) :
    ∃ r ∈ workingRanges w, Region.Sub ⟨off base d, 4⟩ ⟨off base r.1, r.2⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(184, 8), by simp [workingRanges], Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨(184, 8), by simp [workingRanges], Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨(208, 8), by simp [workingRanges], Offset.sub _ (by decide) (by decide)⟩
  all_goals
    exact ⟨(232, 16), by simp [workingRanges], Offset.sub _ (by decide) (by decide)⟩

end VG.Proof.MillerRabin.X86
