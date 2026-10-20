module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # Initialize a generator-two Montgomery exponentiation

Ordinary one is written to array seven, a shared Montgomery product forms
the running Montgomery one, and array five receives ordinary two for the
linear doubling candidate used by each exponent bit.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

def Montgomery.init {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) : Prog isa :=
  VG.Impl.Bignum.Arm.TwoExp.initial (A.op 6 4 7)

theorem init_ok {base : BitVec 32} {len w M : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) (s : State)
    (h : ArithmeticReady base len w s) (hp : P s)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M) :
    WP isa A.init s fun t => Power base len w M 0 t ∧ P t ∧ HeaderKept base s t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have op (i : Nat) (hi : i = 4 ∨ i = 6 ∨ i = 7) : Operand i := by
    rcases hi with rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [Montgomery.init, VG.Impl.Bignum.Arm.TwoExp.initial, WP.seq_iff]
  refine WP.mono (smallConst_ok s (1 : BitVec 32) h (o := 7)
    (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  change numAt u.mem (State.addr base) w 7 = 1 at oneU
  have pu := A.stable frameU restU hp
  have modU := (h.after_array (by decide) keepsU frameU restU readyU.ptr).2.trans modulus
  have r2U := (keeps_array_num keepsU fits (op 4 (by simp)) (by decide)).trans r2
  rw [WP.seq_iff]
  refine WP.mono (A.op_ok u 6 4 7 readyU pu (op 6 (by simp)) (op 4 (by simp)) (op 7 (by simp))
    (by decide) (by rw [oneU]; exact readyU.modulus)) ?_
  rintro v ⟨readyV, modV, boundV, valueV, keepsV, pv, frameV, restV⟩
  rw [modU] at modV boundV valueV
  rw [oneU, Nat.mul_one, r2U] at valueV
  have coprime := coprime_pow2 odd (64 * w)
  have encodedOne : numAt v.mem (State.addr base) w 6 % M = 2 ^ (64 * w) % M := by
    apply mont_cancel coprime
    rw [valueV, Nat.mod_mod, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
  have oneV := (keeps_array_num keepsV fits (op 7 (by simp)) (by decide)).trans oneU
  have r2V := (keeps_array_num keepsV fits (op 4 (by simp)) (by decide)).trans r2U
  refine WP.mono (smallConst_ok v (2 : BitVec 32) readyV (o := 5)
    (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨readyT, twoT, _, keepsT, frameT, restT⟩
  change numAt t.mem (State.addr base) w 5 = 2 at twoT
  have modT := (readyV.after_array (by decide) keepsT frameT restT readyT.ptr).2.trans modV
  have yT := keeps_array_num keepsT fits (op 6 (by simp)) (by decide)
  have oneT := (keeps_array_num keepsT fits (op 7 (by simp)) (by decide)).trans oneV
  have r2T := (keeps_array_num keepsT fits (op 4 (by simp)) (by decide)).trans r2V
  refine ⟨⟨readyT, modT, coprime, by rw [yT]; exact boundV,
    ?_, twoT, oneT, r2T⟩, A.stable frameT restT pv, ?_,
    (frameU.mono (by simpa using A.workspace)).trans
      (frameV.trans (frameT.mono (by simpa using A.workspace))), restU.trans (restV.trans restT)⟩
  · rw [yT, Nat.pow_zero, Nat.one_mul]; exact encodedOne
  · intro d hd
    rw [header_of_keeps readyV keepsT d hd, header_of_keeps readyU keepsV d hd,
      header_of_keeps h keepsU d hd]

end VG.Proof.Bignum.Arm.TwoExp
