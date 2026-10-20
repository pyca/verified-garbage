module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Reuse RSA's Montgomery encoding proof to produce the compact round's
representation of one. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem montOne_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s)
    (modulus : numAt s.mem (State.addr base) w 0 = n) (odd : n % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % n) :
    WP isa (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) s fun t =>
      ArithmeticReady base capacity w t ∧ numAt t.mem (State.addr base) w 0 = n ∧
      numAt t.mem (State.addr base) w 1 = 2 ^ (64 * w) % n ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * capacity := ready.width ▸ ready.layout.2.2.1
  have op (j : Nat) (bound : j = 0 ∨ j = 1 ∨ j = 4) : Operand j := by
    rcases bound with rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 ready (o := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  change numAt u.mem (State.addr base) w 1 = 1 at oneU
  have modulusU := (keeps_array_num keepsU fits (op 0 (by simp)) (by decide)).trans modulus
  have r2U := (keeps_array_num keepsU fits (op 4 (by simp)) (by decide)).trans r2
  refine WP.mono (montEncode_ok u readyU (op 1 (by simp)) (op 1 (by simp)) (by decide)
    modulusU odd r2U) ?_
  rintro t ⟨readyT, modulusT, oneT, _, frameT, restT⟩
  rw [oneU, Nat.one_mul] at oneT
  exact ⟨readyT, modulusT, oneT, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
