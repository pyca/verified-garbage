module

public import VerifiedGarbage.Proof.Rsa.X86.CvFrames

/-! # Initialize all CRT arrays, including their division carry words -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem zeroArrays_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (2 * g.n + 2))) s fun t =>
      Inputs g t ∧ Outside g.base hdr (4 * (nArr * (2 * g.n + 2))) s.mem t.mem ∧
      (∀ j, j < nArr → val32 t.mem g.base (arr (2 * g.n) j) (2 * g.n + 2) = 0) ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have fits := h.ws.fits
  change hdr + nArr * (4 * (2 * g.n + 2)) ≤ g.size at fits
  have fits' : hdr + 4 * (nArr * (2 * g.n + 2)) ≤ g.size := by
    simpa only [Nat.mul_left_comm] using fits
  refine WP.mono (zerosW_ok h.ws.workspace (by unfold nArr; omega) fits') ?_
  rintro t ⟨frame, zero, rest⟩
  have full : Outside g.base 0 g.size s.mem t.mem := frame.mono (by omega) (by omega)
  refine ⟨h.after rest (by decide) (by decide) (h.scratchFrame full), frame, ?_, rest⟩
  intro j hj
  have bound := Nat.mul_le_mul_right (2 * g.n + 2) (show j + 1 ≤ nArr by omega)
  rw [Nat.add_mul, Nat.one_mul] at bound
  have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := j * (2 * g.n + 2)) (c := 2 * g.n + 2) bound
  simpa only [arr, S, Nat.mul_assoc, Nat.mul_left_comm] using part
end VG.Proof.Rsa.X86.CrtValues
