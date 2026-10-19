module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponentArgs
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedValid

/-! # Complete packed-key public RSA body including exponent rejection -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedBody_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) :
    WP isa VG.Impl.Bignum.X86.PrecomputedFn.body s fun t => PrecomputedPost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Bignum.X86.PrecomputedFn.body
  refine WP.seq (WP.mono (precomputedExponentScan_ok h) fun u ⟨E, Lo, Hi, M, K⟩ => ?_)
  refine WP.seq (WP.mono (exponentFlag_ok _ E) fun v ⟨Z, Mv, Kv⟩ => ?_)
  have Ms : v.mem = s.mem := Mv.trans M
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
  refine WP.ite (!Spec.Rsa.exponentValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))) Z ?_ ?_
  · intro bad
    have invalid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = false := by simpa using bad
    refine WP.mono (precomputedFailure_post hv (by
      intro nB _ _
      simp only [Ms, Spec.Rsa.publicOpChecked, invalid, Bool.false_eq_true, ite_false])) fun t ⟨P, T⟩ => ?_
    exact ⟨by simpa only [Ms] using P, Ks.trans T⟩
  · intro good
    have valid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true := by simpa using good
    have bound : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat) < 2 ^ 33 := by
      have H := valid
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at H
      exact H.2
    refine WP.mono (precomputedValid_ok hv (by rw [Ms]) valid bound
      ((Kv.1 .ebx (by decide)).trans Lo) ((Kv.1 .edx (by decide)).trans Hi)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Ms] using R, Ks.trans T⟩

end VG.Proof.Bignum.X86.PublicContext
