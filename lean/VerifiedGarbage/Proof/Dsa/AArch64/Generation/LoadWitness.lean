module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! Loading a padded witness preserves the prepared modulus and exponent. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

theorem loadWitness_ok {s : State} {B p : Addr} {Z w N : Nat} {bs : List Byte}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hp : word s.mem B (8 * kOut) = p)
    (hl : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (h1 : 1 ≤ bs.length) (hw : bs.length ≤ 8 * w) :
    WP isa Impl.Dsa.AArch64.Generation.loadWitness s fun t =>
      ModulusReady t B Z w N ∧ wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧
      Frm B [(slot w aX, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadA_ok h.ws (by decide) (by decide) (by decide) hp hl hsrc rfl h1 hw)
    fun t ⟨hv, ho, _, _, hk⟩ => ?_
  have hf : Frm B [(slot w aX, 8 * (w + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, hv, hf, hk.mono (by decide)⟩
  · intro r hr; rw [List.mem_singleton.mp hr]; exact KMut.ofSlot w aX _
  · intro a ha r hr
    rw [List.mem_singleton.mp hr]
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aN, aOne, aR2, aR1, aRm1, aX] <;> omega_arith
  · intro r hr; rw [List.mem_singleton.mp hr]
    left; simp only [slot, hdrBytes, aX, sMinv]; omega_arith
  · intro r hr; rw [List.mem_singleton.mp hr]
    right; simp only [slot, hdrBytes, aX, aE]; omega_arith

end VG.Proof.Dsa.AArch64.Generation
