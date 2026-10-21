module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.RvResult

import VerifiedGarbage.Proof.Rsa.X86.RvFailure
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Rsa.X86.RvSized
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.TCB.X86.Isa

/-! # Both recovery modulus-validation branches satisfy the shared result definition -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem body_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.body s fun t => Inputs g t ∧ Written g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.body VG.Impl.Rsa.X86.CrtValues.inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 4 (by decide)).readSrc (h.arguments 5 (by decide)).readSrc)
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
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 5).toNat) z ?_ ?_
  · intro accepted
    have modulus : Spec.Rsa.modulusValid (inputValue g v.mem 0)
        (inputBytes g v.mem 0).length = true := by
      rw [mem]
      simp only [inputValue, inputBytes, bytesAt_length, CallGeometry.buffer]
      exact accepted
    have pLen : (g.buffer 0).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.pLen
    have qLen : (g.buffer 2).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.qLen
    refine WP.mono (sized_ok hv len modulus pLen qLen)
      fun t ⟨ht, result, frame, rest⟩ => ?_
    exact ⟨ht, mem ▸ result, mem ▸ frame, keeps.trans rest⟩
  · intro rejected
    have failed : (calculated g s.mem).1 = none := by
      unfold calculated Spec.Rsa.primesKey
      dsimp only
      have ln : (inputBytes g s.mem 0).length = (g.args 5).toNat := bytesAt_length _ _ _
      rw [ln, rejected]
      rfl
    refine WP.mono (failure_ok hv) fun t ⟨ht, p, q, status, frame, rest⟩ => ?_
    exact ⟨ht, written_failure failed p q status, mem ▸ frame, keeps.trans (rest.mono (by decide))⟩

end VG.Proof.Rsa.X86.Recover
