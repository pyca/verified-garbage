module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.CvResult

import VerifiedGarbage.Proof.Rsa.X86.CvFailure
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Both CRT modulus-validation branches satisfy the shared result definition -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.CrtValues (inputArgs)
open VG.Impl.Rsa.X86.CrtValuesRt (body)
open VG.Proof.Rsa.X86.CrtValuesRt (Lengths sized_ok)

theorem body_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa body s fun t => Inputs g t ∧ Written g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold body inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 6 (by decide)).readSrc (h.arguments 7 (by decide)).readSrc)
    fun u ⟨p, c, m, k⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u len.lower len.upper
    (by rw [p]; exact h.inputFit 0)
    (by rw [p, k.2.1, k.2.2]; exact h.inputRead 0)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun v ⟨z, mv, kv⟩ => ?_)
  rw [p, m] at z
  have mem : v.mem = s.mem := mv.trans m
  have keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (k.mono (by decide)).trans (kv.mono (by decide))
  have hv := h.after keeps (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 7).toNat) z ?_ ?_
  · intro accepted
    refine WP.mono (sized_ok hv len) fun t ⟨ht, result, frame, rest⟩ => ?_
    rw [mem] at result frame
    refine ⟨ht, written_arithmetic result ?_ ?_ ?_ ?_ ?_ ?_, frame, keeps.trans rest⟩
    · simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact accepted
    · simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact len.pSmall
    · simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact len.qSmall
    · simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.dpLen
    · simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.dqLen
    · simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.qiLen
  · intro rejected
    have failed : calculated g s.mem = none := by
      unfold calculated Spec.Rsa.crtKey
      have ln : (inputBytes g s.mem 0).length = (g.args 7).toNat := bytesAt_length _ _ _
      rw [ln]
      simp only [rejected, Bool.false_eq_true, false_and, ite_false]
    refine WP.mono (failure_ok hv) fun t ⟨ht, dp, dq, qi, status, frame, rest⟩ => ?_
    refine ⟨ht, ?_, mem ▸ frame, keeps.trans (rest.mono (by decide))⟩
    unfold Written
    rw [failed]
    refine ⟨status, ?_⟩
    simp only [outputBuffers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩

end VG.Proof.Rsa.X86.CrtValues
