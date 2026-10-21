module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Clear an arbitrary bank of native RSA key arrays

The same lemma initializes the full key workspace and the smaller bank
used for prime-width or two-word public-exponent inversions.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

theorem zero_arrays {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) (positive : 0 < N) :
    WP isa (VG.Impl.Mont.X86.Dynamic.zerosW hdr (N * (n + 2))) s fun t =>
      Ws t B Z n N ∧ Outside B hdr (4 * (N * (n + 2))) s.mem t.mem ∧
      (∀ j, j < N → val32 t.mem B (arr n j) (n + 2) = 0) ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have bound := h.fits
  change hdr + N * (4 * (n + 2)) ≤ Z at bound
  have fits : hdr + 4 * (N * (n + 2)) ≤ Z := by
    simpa only [Nat.mul_left_comm] using bound
  refine WP.mono (zerosW_ok h.workspace (Nat.mul_pos positive (by omega)) fits)
    fun t ⟨frame, zero, K⟩ => ?_
  refine ⟨h.rest K, frame, ?_, K⟩
  intro j hj
  have partBound := Nat.mul_le_mul_right (n + 2) (show j + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at partBound
  have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero
    (a := j * (n + 2)) (c := n + 2) partBound
  simpa only [arr, S, Nat.mul_assoc, Nat.mul_left_comm] using part

end VG.Proof.RsaKeyGen.X86.Key
