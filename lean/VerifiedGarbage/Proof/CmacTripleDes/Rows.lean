/-!
# Words that are constant on each row

The S-box checks (`Proof/CmacTripleDes/<Target>/Round.lean`) give each
input slot the value that is, on row `c`, all ones if bit `t` of `c` is set
and zero otherwise. Built a row at a time (`rowsOf`), the kernel evaluates
it in one step per row, rather than one per bit (`tableOf`).
-/

namespace VG.Proof.CmacTripleDes

/-- Lanes of `w` bits: lane `c < n` is all ones if `f c`, else zero. -/
def rowsOf (w : Nat) (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => rowsOf w f n ||| if f n then (2 ^ w - 1) <<< (w * n) else 0

theorem testBit_rowsOf (w : Nat) (f : Nat → Bool) (n i : Nat) :
    (rowsOf w f n).testBit i = (decide (i < w * n) && f (i / w)) := by
  induction n with
  | zero => simp [rowsOf]
  | succ n ih =>
    rw [rowsOf, Nat.testBit_or, ih]
    have hlane : ((2 ^ w - 1) <<< (w * n)).testBit i = (decide (w * n ≤ i) && decide (i < w * (n + 1))) := by
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases h : w * n ≤ i <;> simp only [h, decide_true, decide_false, Bool.true_and, Bool.false_and]
      congr 1; apply propext; rw [Nat.mul_succ]; omega
    by_cases hi : i < w * n
    · have : ¬ w * n ≤ i := by omega
      cases f n <;> simp [hi, hlane, this, Nat.lt_of_lt_of_le hi (Nat.mul_le_mul_left w (Nat.le_succ n))]
    · by_cases hi' : i < w * (n + 1)
      · have hd : i / w = n := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega)
          (by rw [Nat.mul_comm]; exact hi')
        cases hf : f n <;> simp [hi, hi', hd, hf, hlane, Nat.le_of_not_lt hi]
      · cases f n <;> simp [hi, hi', hlane]

end VG.Proof.CmacTripleDes
