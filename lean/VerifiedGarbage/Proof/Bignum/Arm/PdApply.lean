module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdArithmetic

import VerifiedGarbage.Proof.Bignum.Arm.PdInputImport
import VerifiedGarbage.Proof.Bignum.Arm.PdAccept
import VerifiedGarbage.Proof.Bignum.Arm.PdFinish
import VerifiedGarbage.Proof.Bignum.Arm.PdControls
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # The complete checked-input RSA arithmetic path, from bytes to masked output -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdApply_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdArithmetic base dst np ep xp len k eLen N R eb xb s) :
    WP isa PublicFn.applyInput s fun t =>
      (pdGood k N R → N < 2 ^ (8 * k) → Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if Spec.Rsa.os2ip xb < N then
          Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (N)) k
         else List.replicate k 0)) ∧
      t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < N)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.applyInput, WP.seq_iff]
  refine WP.mono (pdInputImport_ok s h) ?_
  rintro u ⟨operand, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (pdAccept_ok u operand) ?_
  rintro v ⟨accepted, frameV, restV⟩
  rw [restU.sp] at frameV
  rw [WP.seq_iff]
  refine WP.mono (pdControls_ok v accepted) ?_
  rintro z ⟨controlled, phase, frameZ, restZ⟩
  rw [WP.seq_iff]
  refine WP.mono (pdExponentiate_ok z controlled phase) ?_
  rintro q ⟨result, frameQ, restQ⟩
  refine WP.mono (pdFinish_ok q result) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  exact ⟨bytes, status,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans
      ((frameZ.mono (by simp)).trans ((frameQ.mono (by simp)).trans (frameT.mono (by simp))))),
    restU.trans (restV.trans (restZ.trans (restQ.trans restT)))⟩

end VG.Proof.Bignum.Arm
