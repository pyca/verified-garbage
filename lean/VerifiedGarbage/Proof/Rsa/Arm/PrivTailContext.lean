module

import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckRegions
public import VerifiedGarbage.Proof.Rsa.Arm.PrivTail
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # The call context supplies every bound and retained argument for release -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem PrivContext.tailInput {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    TailInput g.output g.temporary (g.sources 2) g.length s := by
  have low := h.valid.minLength
  have high := h.valid.maxLength
  have stackFit := h.valid.stackHigh
  refine ⟨⟨by omega, by omega, by rw [h.sp]; simp only [frameBytes] at stackFit; omega,
    ?_, ?_, ?_, ?_, by rw [h.sp]; rfl, h.valid.temporaryFit, h.valid.outputFit,
    h.temporaryWrite, h.outputWrite, ?_⟩, ?_, ?_, h.valid.sourceFits 2, (h.sources 2).read⟩
  · rw [h.sp]; exact h.inner.read (by decide)
  · rw [h.sp]; exact h.inner.read (by decide)
  · rw [h.sp]; exact slots 0 (by decide)
  · rw [h.sp]; exact slots 2 (by decide)
  · rw [temporary_region h.valid]
    exact (innerSlice_external h.valid (d := oM) (n := g.length)
      (by simp only [oM, frameBytes]; omega)).1
  · rw [h.sp]; exact h.inner
  · rw [h.sp]; exact slots 5 (by decide)

theorem tailWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ (r : Region), r ∈ [⟨State.addr g.output, g.length⟩, ⟨State.addr g.temporary, g.length⟩] →
      ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [temporary_region h]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [oM, frameBytes]; omega)
end VG.Proof.Rsa.Arm
