module
public import VerifiedGarbage.Proof.Rsa.X86.RvInputs

import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # Initialize all recovery arrays, including their division carry words -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem zeroArrays_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (g.toGeo.w + 2))) s fun t =>
      Inputs g t ∧ Outside g.B hdr (4 * (nArr * (g.toGeo.w + 2))) s.mem t.mem ∧
      (∀ j, j < nArr → val32 t.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) = 0) ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have fits := h.ws.fits
  change hdr + nArr * (4 * (g.toGeo.w + 2)) ≤ g.Z at fits
  have fits' : hdr + 4 * (nArr * (g.toGeo.w + 2)) ≤ g.Z := by
    simpa only [Nat.mul_left_comm] using fits
  refine WP.mono (zerosW_ok h.ws.workspace (by unfold nArr; omega) fits') ?_
  rintro t ⟨frame, zero, rest⟩
  have full : Outside g.B 16 (g.Z - 16) s.mem t.mem := frame.mono (by unfold hdr; omega) (by have := h.ws.hdr_le; unfold hdr at this; omega)
  refine ⟨h.after rest (by decide) (by decide) (h.scratchFrame full), frame, ?_, rest⟩
  intro j hj
  have bound := Nat.mul_le_mul_right (g.toGeo.w + 2) (show j + 1 ≤ nArr by omega)
  rw [Nat.add_mul, Nat.one_mul] at bound
  have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := j * (g.toGeo.w + 2)) (c := g.toGeo.w + 2) bound
  simpa only [arr, S, Nat.mul_assoc, Nat.mul_left_comm] using part
end VG.Proof.Rsa.X86.Recover
