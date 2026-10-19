module

import VerifiedGarbage.Proof.Bignum.Arm.PdCheckFirst
public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckRest
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete public validation of the arithmetic preconditions for packed RSA keys -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdChecks_ok (s : State) {base : BitVec 32} {len w N R : Nat}
    (h : PdCheckState base len w N R s) :
    WP isa pdChecks s fun t =>
      PdCheckState base len w N R t ∧ t.gpr .r11 = BitVec.ofNat 32 (pdAccepted N R).toNat ∧
      t.z = !(pdAccepted N R) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  unfold pdChecks
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (pdCheckFirst_ok s h) ?_
  rintro u ⟨hu, first, frameU, restU⟩
  refine WP.mono (pdCheckRest_ok u hu first) ?_
  rintro t ⟨ht, accepted, zero, frameT, restT⟩
  rw [restU.sp] at frameT
  exact ⟨ht, accepted, zero, (frameU.mono (by simp)).trans frameT, restU.trans restT⟩

theorem pdAccepted_facts {N R : Nat} (h : pdAccepted N R = true) : 1 < N ∧ R < N ∧ N % 2 = 1 := by
  simpa only [pdAccepted, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

end VG.Proof.Bignum.Arm
