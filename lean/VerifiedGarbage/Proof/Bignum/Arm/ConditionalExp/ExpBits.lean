module
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpRound
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Eight verified bit steps append one byte to the RSA exponent -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
variable {ok : Prop} {Q : State → Prop} {regions : List Region}

structure ExpBitState (ok : Prop) (base : BitVec 32) (len w M x E v j : Nat) (s : State) : Prop where
  power : ExpState ok base len w M x (E * 2 ^ j + v / 2 ^ (8 - j)) s
  byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 (v * 2 ^ j)
  count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 192) 32 = BitVec.ofNat 32 (8 - j)

theorem expBitState_step (s : State) {base : BitVec 32} {len w M x E v j : Nat}
    (K : TwoExp.Montgomery base len w Q regions)
    (h : ExpBitState ok base len w M x E v j s) (q : Q s) (hv : v < 256) (hj : j < 8) :
    WP isa (expBitRoundWith K.op) s fun t => ExpBitState ok base len w M x E v (j + 1) t ∧ Q t ∧
      t.z = decide (j + 1 = 8) ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega_using [hj] : j ≤ 7)
  have valueFit : v * 2 ^ j < 2 ^ 32 := by
    have := Nat.mul_le_mul_left v hp
    omega_using [hv, this]
  refine WP.mono (expRound_ok s K h.power q valueFit (by omega_using [hj]) (by omega_using []) h.byte h.count) ?_
  rintro t ⟨power, qt, byte, count, zero, header, frame, rest⟩
  have expEq : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
    rw [Nat.mul_add, Nat.add_assoc, bit_step hj, show 7 - j = 8 - (j + 1) by omega_using [],
      Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]
  rw [expEq] at power
  refine ⟨⟨power, ?_, ?_⟩, qt, ?_, header, frame, rest⟩
  · rw [byte, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
  · rw [count]; congr 1
  · rw [zero]; exact decide_eq_decide.mpr (by omega_using [])

theorem expBits_ok (s : State) {base : BitVec 32} {len w M x E v : Nat}
    (K : TwoExp.Montgomery base len w Q regions)
    (h : ExpBitState ok base len w M x E v 0 s) (q : Q s) (hv : v < 256) :
    WP isa (expBitsWith K.op) s fun t => ExpState ok base len w M x (256 * E + v) t ∧ Q t ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ ExpBitState ok base len w M x E v j t ∧ Q t ∧
    (∀ d, d + 4 ≤ 192 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
      s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
    Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold expBitsWith
  refine WP.loop (M := isa) I ?_ 8 s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, state, qt, header, frame, rest⟩ := inv
    refine WP.mono (expBitState_step t K state qt hv (by omega_using [jk, hk])) ?_
    rintro u ⟨next, qu, zero, headerU, frameU, restU⟩
    have headerAll := fun d hd => (headerU d hd).trans (header d hd)
    by_cases last : j + 1 = 8
    · left
      refine ⟨?_, ?_, qu, headerAll, frame.trans frameU, rest.trans restU⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · have power := next.power
        simpa only [last, Nat.sub_self, Nat.pow_zero, Nat.div_one, show 2 ^ 8 = 256 from rfl,
          Nat.mul_comm E 256] using power
    · right
      refine ⟨?_, k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, last], next, qu, headerAll, frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · exact ⟨0, by decide, by decide, h, q, fun _ _ => rfl, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm.ConditionalExp
