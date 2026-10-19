module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare

import VerifiedGarbage.Proof.Bignum.Arm.PublicValid
import VerifiedGarbage.Proof.Bignum.Arm.PublicFail
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Framework.Block

/-! # Validate the public modulus and implement both outcomes of the checked RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicModulus_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s)
    (exponent : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true) :
    WP isa PublicFn.modulus s fun t =>
      Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.modulus, WP.seq_iff]
  refine WP.mono (pcInputs_ok s h.stack.pcStack) ?_
  rintro u ⟨source, count, memU, restU⟩
  have hu := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  rw [WP.seq_iff]
  refine WP.mono (modulusCheck_ok u hu.buffers.minLength hu.buffers.maxLength hu.buffers.modulus.fits
    hu.buffers.modulus.read source count) ?_
  rintro v ⟨flag, memV, restV⟩
  rw [hu.buffers.modulus.bytes] at flag
  have hv := hu.of_mem memV restV ((restV.gpr .r0 (by simp)).trans hu.ptr)
  have rest : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (restV.mono (by simp [roundClobbers]))
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) (by change some v.z = _; rw [flag]) ?_ ?_
  · intro valid
    have input : PublicValidInput base dst np ep xp len k eLen nb eb xb v :=
      ⟨hv, valid, (restV.gpr .r4 (by simp)).trans source, (restV.gpr .r6 (by simp)).trans count⟩
    refine WP.mono (publicValid_ok v input exponent) ?_
    rintro t ⟨result, frame, restT⟩
    rw [memV, memU, rest.sp] at frame
    exact ⟨result, frame, rest.trans restT⟩
  · intro invalid
    refine WP.mono (publicFail_ok v hv) ?_
    rintro t ⟨status, bytes, frame, restT⟩
    have failed : Spec.Rsa.publicOpChecked nb eb xb = none := by
      simp only [Spec.Rsa.publicOpChecked, exponent, ite_true, Spec.Rsa.publicOp,
        h.buffers.modulus.length, invalid, Bool.false_eq_true, ite_false]
    rw [failed]
    rw [memV, memU] at frame
    exact ⟨⟨status, bytes⟩, frame.mono (by simp), rest.trans restT⟩

end VG.Proof.Bignum.Arm
