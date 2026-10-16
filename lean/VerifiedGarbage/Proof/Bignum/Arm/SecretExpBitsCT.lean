module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpRoundCT
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpBits
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Eight private exponent-bit steps have a secret-independent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem secretExpBits_ct {base : BitVec 32} {len w M1 M2 x1 x2 E1 E2 v1 v2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hv1 : v1 < 256) (hv2 : v2 < 256) :
    RelCT isa (fun s t => ExpBitState base len w M1 x1 E1 v1 0 s ∧
      ExpBitState base len w M2 x2 E2 v2 0 t ∧ s.sp = t.sp) secretExpBits (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧
    ExpBitState base len w M1 x1 E1 v1 j s ∧ ExpBitState base len w M2 x2 E2 v2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) secretExpRound fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have hj : j < 8 := by omega
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : j ≤ 7)
    have valueFit1 : v1 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v1 hp; omega
    have valueFit2 : v2 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v2 hp; omega
    have ct := relCT_keep_sp (secretExpRound_ct (base := base) (len := len) (w := w)
      (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (E1 := E1 * 2 ^ j + v1 / 2 ^ (8 - j))
      (E2 := E2 * 2 ^ j + v2 / 2 ^ (8 - j)) fit valueFit1 valueFit2) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨⟨hs.power, hs.byte⟩, ⟨ht.power, ht.byte⟩, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _, _⟩ := secretExpBitState_step s hs hv1 hj
    obtain ⟨_, _, run2, next2, zero2, _, _, _⟩ := secretExpBitState_step t ht hv2 hj
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
  exact (RelCT.loop I step 8).mono
    (fun _ _ h => ⟨0, by decide, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
