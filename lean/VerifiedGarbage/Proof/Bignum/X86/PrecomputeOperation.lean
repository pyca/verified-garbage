module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeFailure
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Public precomputation succeeds exactly for valid moduli -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputeFailure_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s)
    (invalid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = false) :
    WP isa PrecomputeFn.failure s fun t => PrecomputePost base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have twice : 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len := by omega
  refine WP.mono (precomputeFailure_ok (n := 2 * Spec.Rsa.modulusWords len) (by omega) (by omega)
    (by simpa only [twice] using h.outFit) ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.preLen]; exact (h.stack 1 (by decide)).readSrc)
    (by simpa only [twice] using h.outWrite)) fun t ⟨B, Y, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · simp only [Spec.Rsa.publicPrecompute, bytesAt_length, invalid, Bool.false_eq_true, ite_false]
    exact ⟨B, Y⟩
  · have F := outside_frame O (by omega)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [twice])

theorem precomputeBody_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s) :
    WP isa PrecomputeFn.body s fun t => PrecomputePost base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PrecomputeFn.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower h.upper (by rw [P]; exact h.nFit)
    (by rw [P, K.2.1, K.2.2]; exact h.nRead) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Ms : v.mem = s.mem := Mv.trans M
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
  have sp : v.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len) Z ?_ ?_
  · intro valid
    refine WP.mono (precomputeValid_ok hv (by rw [Ms]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Ms, sp] using R, Ks.trans T⟩
  · intro invalid
    refine WP.mono (precomputeFailure_post hv (by rw [Ms]; exact invalid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Ms, sp] using R, Ks.trans T⟩

end VG.Proof.Bignum.X86.PublicContext
