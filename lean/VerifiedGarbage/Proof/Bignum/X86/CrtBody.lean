module
public import VerifiedGarbage.Proof.Bignum.X86.CrtPost

import VerifiedGarbage.Proof.Bignum.X86.CrtValid
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs

/-! # Private CRT rejects invalid public moduli before processing private data -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem body_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s) :
    WP isa Crt.body s fun t => Post base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nf := h.fits 2 (by decide)
  have nr := h.readable 2 (by decide)
  change (args 2).toNat + (args 3).toNat ≤ 2 ^ 32 at nf
  change InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (args 3).toNat at nr
  rw [h.modulus_length] at nf nr
  unfold Crt.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower h.upper (by rw [P]; exact nf)
    (by rw [P, K.2.1, K.2.2]; exact nr) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  have modulus : componentValue s.mem args 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) := by
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) (args 3).toNat) = _
    rw [h.modulus_length]
  rw [← modulus] at Z
  refine WP.ite (Spec.Rsa.modulusValid (componentValue s.mem args 2) len) Z ?_ ?_
  · intro valid
    refine WP.mono (valid_ok hv (by rw [Msv]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv] using R, Ksv.trans T⟩
  · intro invalid
    have failed : specResult v.mem args = none := by
      rw [specResult_eq, Msv, h.modulus_length, invalid]
      rfl
    refine WP.mono (failure_post hv failed) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv] using R, Ksv.trans T⟩

end VG.Proof.Bignum.X86.Crt
