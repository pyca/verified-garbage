import VerifiedGarbage.Spec.Cast5

/-!
# CAST5: rotation by a secret amount, in five masked steps

The implementations rotate `I` left by `Kr mod 32` (§2.2) without using the
secret amount as a shift count: in step `b` (0–4) they rotate by `2 ^ b`, and
keep the rotated value only if bit `b` of `Kr` is set, under a mask
(`step`). Whatever the order of the steps, the result is the rotation by
the sum of the kept amounts, `Kr mod 32` (`steps_eq`).
-/

namespace VG.Proof.Cast5

/-- Bit `i` of the rotation of `x` left by `r < 32`. -/
theorem getLsbD_rotateLeft_lt (x : BitVec 32) {r i : Nat} (hr : r < 32) (hi : i < 32) :
    (x.rotateLeft r).getLsbD i = if i < r then x.getLsbD (32 - r + i) else x.getLsbD (i - r) := by
  rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hr, decide_eq_true hi, Bool.true_and]

theorem rotateLeft_rotateLeft_lt (x : BitVec 32) {m n : Nat} (hm : m < 32) (hn : n < 32) :
    (x.rotateLeft m).rotateLeft n = x.rotateLeft ((m + n) % 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rotateLeft_lt _ hn hi, getLsbD_rotateLeft_lt _ (Nat.mod_lt _ (by decide)) hi]
  split
  · rw [getLsbD_rotateLeft_lt _ hm (by omega_arith)]
    repeat' split
    all_goals first | omega_arith | exact congrArg _ (by omega_arith)
  · rw [getLsbD_rotateLeft_lt _ hm (by omega_arith)]
    repeat' split
    all_goals first | omega_arith | exact congrArg _ (by omega_arith)

/-- Rotations compose. -/
theorem rotateLeft_rotateLeft (x : BitVec 32) (m n : Nat) :
    (x.rotateLeft m).rotateLeft n = x.rotateLeft (m + n) := by
  rw [← BitVec.rotateLeft_mod_eq_rotateLeft (r := n), ← BitVec.rotateLeft_mod_eq_rotateLeft (r := m),
    rotateLeft_rotateLeft_lt _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
    ← BitVec.rotateLeft_mod_eq_rotateLeft (r := m + n)]
  congr 1
  omega_arith

theorem rotateRight_eq_rotateLeft (x : BitVec 32) {n : Nat} (h0 : 0 < n) (hn : n ≤ 32) :
    x.rotateRight (32 - n) = x.rotateLeft n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt (show 32 - n < 32 by omega_arith),
    decide_eq_true hi, Bool.true_and, Bool.true_and]
  by_cases h : n = 32
  · subst h
    simp only [Nat.sub_self, Nat.mod_self, Nat.not_lt_zero, ite_false, Nat.sub_zero,
      Nat.zero_add]
    split <;> first | omega_arith | exact congrArg _ (by omega_arith)
  · rw [Nat.mod_eq_of_lt (show n < 32 by omega_arith)]
    repeat' split
    all_goals first | omega_arith | exact congrArg _ (by omega_arith)

/-- Step `b` of the rotation of `a` by `k`: rotate by `2 ^ b` (as a rotation
right by `32 - 2 ^ b`), keeping it under the mask that is zero exactly if
bit `b` of `k` (bit 0 of `kb`, `k` shifted right by `b`) is set. -/
def step (a kb : BitVec 32) (b : Nat) : BitVec 32 :=
  ((a ^^^ a.rotateRight (32 - 2 ^ b)) &&& ((kb &&& 1) - 1)) ^^^ a.rotateRight (32 - 2 ^ b)

theorem and_one_toNat (kb : BitVec 32) : (kb &&& 1).toNat = kb.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem step_eq (a kb : BitVec 32) {b : Nat} (hb : b < 5) :
    step a kb b = a.rotateLeft (2 ^ b * (kb.toNat % 2)) := by
  have hr : a.rotateRight (32 - 2 ^ b) = a.rotateLeft (2 ^ b) :=
    rotateRight_eq_rotateLeft a (Nat.pow_pos (by decide)) (by
      rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_arith) with h | h | h | h | h <;>
        subst h <;> decide)
  unfold step
  rw [hr]
  rcases Nat.mod_two_eq_zero_or_one kb.toNat with h | h
  · have : (kb &&& 1) - 1 = BitVec.allOnes 32 := by
      have : kb &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [and_one_toNat, h]; rfl)
      rw [this]; rfl
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, h,
      Nat.mul_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_rotateLeft_lt _ (by decide) hi]
    simp
  · have : (kb &&& 1) - 1 = 0 := by
      have : kb &&& 1 = 1 := BitVec.eq_of_toNat_eq (by rw [and_one_toNat, h]; rfl)
      rw [this]; rfl
    rw [this, show ∀ y : BitVec 32, y &&& 0 = 0 from fun y => BitVec.eq_of_getLsbD_eq (by simp),
      show ∀ y : BitVec 32, 0 ^^^ y = y from fun y => BitVec.eq_of_getLsbD_eq (by simp), h,
      Nat.mul_one]

/-- The five steps, with `k` shifted right by `b` before step `b`, rotate by
`k mod 32`. -/
theorem steps_eq (a k : BitVec 32) :
    step (step (step (step (step a k 0) (k >>> 1) 1) (k >>> 1 >>> 1) 2)
      (k >>> 1 >>> 1 >>> 1) 3) (k >>> 1 >>> 1 >>> 1 >>> 1) 4 = a.rotateLeft (k.toNat % 32) := by
  simp only [step_eq _ _ (show 0 < 5 by decide), step_eq _ _ (show 1 < 5 by decide),
    step_eq _ _ (show 2 < 5 by decide), step_eq _ _ (show 3 < 5 by decide),
    step_eq _ _ (show 4 < 5 by decide), rotateLeft_rotateLeft, BitVec.toNat_ushiftRight]
  congr 1
  simp only [Nat.shiftRight_eq_div_pow]
  omega_arith

/-- Step `b` as a selection: the rotation by `2 ^ b` if bit 0 of `kb` is set. -/
def selStep (a kb : BitVec 32) (b : Nat) : BitVec 32 :=
  if (kb &&& 1) = 0 then a else a.rotateRight (32 - 2 ^ b)

theorem selStep_eq_step (a kb : BitVec 32) {b : Nat} (hb : b < 5) : selStep a kb b = step a kb b := by
  have hr : a.rotateRight (32 - 2 ^ b) = a.rotateLeft (2 ^ b) :=
    rotateRight_eq_rotateLeft a (Nat.pow_pos (by decide)) (by
      rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_arith) with h | h | h | h | h <;>
        subst h <;> decide)
  rw [step_eq _ _ hb, selStep]
  rcases Nat.mod_two_eq_zero_or_one kb.toNat with h | h
  · rw [ite_eq_left (BitVec.eq_of_toNat_eq (by rw [and_one_toNat, h]; rfl)), h, Nat.mul_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_rotateLeft_lt _ (by decide) hi]
    simp
  · have hne : ¬(kb &&& 1) = 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [and_one_toNat, h] at this
      exact absurd this (by decide)
    rw [ite_eq_right hne, h, Nat.mul_one, hr]

end VG.Proof.Cast5
