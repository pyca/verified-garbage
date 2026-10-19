module

import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicValid
public import VerifiedGarbage.Proof.Bignum.X86.PublicPost
import VerifiedGarbage.Spec.RsaKeyGen

/-! # Exponent validation selects a fully checked public operation or zero output -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem checkExponent_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s)
    (modulus : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa PublicFn.checkExponent s fun t => PublicPost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PublicFn.checkExponent
  refine WP.seq (WP.mono (publicExponent_ok h) fun u ⟨E, Lo, Hi, M, K⟩ => ?_)
  refine WP.seq (WP.mono (exponentFlag_ok _ E) fun v ⟨Z, Mv, Kv⟩ => ?_)
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  refine WP.ite (!Spec.Rsa.exponentValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))) Z ?_ ?_
  · intro bad
    have invalid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = false := by
      simpa using bad
    refine WP.mono (publicFailure_post hv (by simp only [Msv, Spec.Rsa.publicOpChecked, invalid, Bool.false_eq_true, ite_false]))
      fun t ⟨P, T⟩ => ?_
    exact ⟨by simpa only [Msv] using P, Ksv.trans T⟩
  · intro good
    have valid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true := by
      simpa using good
    have bound : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat) < 2 ^ 33 := by
      have H := valid
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at H
      exact H.2
    refine WP.mono (publicValid_ok hv (by rw [Msv]; exact modulus) bound
      ((Kv.1 .ebx (by decide)).trans Lo) ((Kv.1 .edx (by decide)).trans Hi))
      fun t ⟨R, T⟩ => ?_
    rw [Msv] at R
    exact ⟨R.written modulus valid, Ksv.trans T⟩

end VG.Proof.Bignum.X86.PublicContext
