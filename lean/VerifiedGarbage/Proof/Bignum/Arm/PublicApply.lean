module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic

import VerifiedGarbage.Proof.Bignum.Arm.PublicImport
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccept
import VerifiedGarbage.Proof.Bignum.Arm.PublicFinish
import VerifiedGarbage.Proof.Bignum.Arm.PublicControls
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # The complete checked-input RSA arithmetic path, from bytes to masked output -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicApply_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicArithmetic base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.applyInput s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
          Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip nb)) k
         else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.applyInput, WP.seq_iff]
  refine WP.mono (publicImport_ok s h) ?_
  rintro u ⟨operand, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (publicAccept_ok u operand) ?_
  rintro v ⟨accepted, frameV, restV⟩
  rw [restU.sp] at frameV
  rw [WP.seq_iff]
  refine WP.mono (publicControls_ok v accepted) ?_
  rintro z ⟨controlled, phase, frameZ, restZ⟩
  rw [WP.seq_iff]
  refine WP.mono (publicExponentiate_ok z controlled phase) ?_
  rintro q ⟨result, frameQ, restQ⟩
  refine WP.mono (publicFinish_ok q result) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  exact ⟨bytes, status,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans
      ((frameZ.mono (by simp)).trans ((frameQ.mono (by simp)).trans (frameT.mono (by simp))))),
    restU.trans (restV.trans (restZ.trans (restQ.trans restT)))⟩

end VG.Proof.Bignum.Arm
