module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCheckExponent
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck

/-! # Complete checked public RSA body, including invalid-modulus rejection -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem publicBody_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) :
    WP isa PublicFn.body s fun t => PublicPost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PublicFn.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower h.upper (by rw [P]; exact h.nFit)
    (by rw [P, K.2.1, K.2.2]; exact h.nRead) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len)
    Z ?_ ?_
  · intro valid
    refine WP.mono (checkExponent_ok hv (by rw [Msv]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv] using R, Ksv.trans T⟩
  · intro invalid
    have failed : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt v.mem (byteAddr (args 2)) len)
        (Spec.Rsa.bytesAt v.mem (byteAddr (args 4)) (args 5).toNat)
        (Spec.Rsa.bytesAt v.mem (byteAddr (args 6)) len) = none := by
      simp only [Msv, Spec.Rsa.publicOpChecked, Spec.Rsa.publicOp, bytesAt_length, invalid,
        Bool.false_eq_true, ite_false, ite_self]
    refine WP.mono (publicFailure_post hv failed) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv] using R, Ksv.trans T⟩

end VG.Proof.Bignum.X86.PublicContext
