module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedApplyInput
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedAcceptance

/-! # A well-formed stored key yields the shared checked-public RSA result -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedApply_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (N : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) =
      wv s.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len))
    (R : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) =
      wv s.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len))
    (E : val32 s.mem base 128 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
    (validE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true)
    (accepted : precomputedAccepted (wv s.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len))
      (wv s.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len)) = true) :
    WP isa (VG.Impl.Bignum.X86.PrecomputedFn.applyInput (Spec.Rsa.modulusWords len)) s fun t =>
      PrecomputedPost base bytes len args s.mem t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have facts := of_decide_eq_true accepted
  refine WP.mono (precomputedApplyInput_ok h N R E facts.1 facts.2.2 facts.2.1) fun t ⟨B, Y, F, K⟩ => ?_
  refine ⟨⟨?_, F⟩, K⟩
  intro nB length key
  obtain ⟨valid, modulus, power⟩ := pre_of_some length h.lower key
  change wv s.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len) = Spec.Rsa.os2ip nB at modulus
  change wv s.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len) =
    2 ^ (128 * Spec.Rsa.modulusWords len) % Spec.Rsa.os2ip nB at power
  have fit : Spec.Rsa.os2ip nB < 2 ^ (8 * len) := by
    have bound := os2ip_lt nB
    simpa only [length, pow256_eq] using bound
  have Output := Y (by rw [modulus]; exact power) (by rw [modulus]; exact fit)
  rw [modulus] at B Output
  apply publicOutput_written length valid validE ?_ B
  rw [powMod_eq]
  split <;> simp_all only [ite_true, ite_false, i2osp_zero']

end VG.Proof.Bignum.X86.PublicContext
