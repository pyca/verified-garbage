module

public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# RSASSA-PSS verification on PPC64LE: the shift, as views

Untrusted: everything here is checked by Lean. A pass of the shift
(`passV`) replaces each of `n` bytes from `b` by the one `d` bytes after it,
or none, by one bit. Ten passes by the bits of `a < 2^10`, the `j`-th by
`2^j` (`shV`), shift the `n` bytes left by `a`, zeros coming in from after
them (`shV_eq`), if the `2^9` bytes after them are zero.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG
open VG.Proof.Mgf1 (ifp ifn)

/-- A pass: the `n` bytes from `b` replaced by those `d` after them if
`bit`. -/
def passV (V : Nat → Byte) (b n : Nat) (bit : Bool) (d : Nat) (o : Nat) : Byte :=
  if b ≤ o ∧ o < b + n then (if bit then V (o + d) else V o) else V o

/-- The first `j` passes by the bits of `a`. -/
def shV (V : Nat → Byte) (b n a : Nat) : Nat → Nat → Byte
  | 0 => V
  | j + 1 => passV (shV V b n a j) b n (a / 2 ^ j % 2 = 1) (2 ^ j)

theorem shV_out (V : Nat → Byte) (b n a : Nat) : ∀ j o, ¬ (b ≤ o ∧ o < b + n) → shV V b n a j o = V o
  | 0, _, _ => rfl
  | j + 1, o, h => by rw [shV, passV, ifn h, shV_out V b n a j o h]

theorem shV_in (V : Nat → Byte) (b n a : Nat) (hz : ∀ x, n ≤ x → x < n + 2 ^ 9 → V (b + x) = 0) :
    ∀ j ≤ 10, ∀ i < n, shV V b n a j (b + i) = if i + a % 2 ^ j < n then V (b + (i + a % 2 ^ j)) else 0
  | 0, _, i, hi => by simp only [shV, Nat.pow_zero, Nat.mod_one, Nat.add_zero]; rw [ifp hi]
  | j + 1, hj, i, hi => by
    have ih := shV_in V b n a hz j (by omega)
    have hm : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * (a / 2 ^ j % 2) := Nat.mod_pow_succ
    have h2 := Nat.mod_lt (a / 2 ^ j) (show 0 < 2 by decide)
    have hp : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    have hp10 : (2 : Nat) ^ 10 = 1024 := rfl
    have hp9 : (2 : Nat) ^ 9 = 512 := rfl
    have hmj := Nat.mod_lt a (Nat.two_pow_pos j)
    rw [shV, passV, ifp ⟨by omega, by omega⟩]
    by_cases hb : a / 2 ^ j % 2 = 1
    · rw [ifp (decide_eq_true hb), show b + i + 2 ^ j = b + (i + 2 ^ j) by omega]
      rw [hb, Nat.mul_one] at hm
      rw [hm]
      by_cases hl : i + 2 ^ j < n
      · rw [ih (i + 2 ^ j) hl, show i + 2 ^ j + a % 2 ^ j = i + (a % 2 ^ j + 2 ^ j) by omega]
      · rw [shV_out V b n a j _ (by omega), hz _ (by omega) (by omega), ifn (by omega)]
    · have hb0 : a / 2 ^ j % 2 = 0 := by omega
      rw [ifn (by simpa using hb), hm, hb0, Nat.mul_zero, Nat.add_zero, ih i hi]

/-- Ten passes shift the `n` bytes left by `a`. -/
theorem shV_eq (V : Nat → Byte) {b n a : Nat} (ha : a < 2 ^ 10)
    (hz : ∀ x, n ≤ x → x < n + 2 ^ 9 → V (b + x) = 0) {i : Nat} (hi : i < n) :
    shV V b n a 10 (b + i) = if i + a < n then V (b + (i + a)) else 0 := by
  rw [shV_in V b n a hz 10 (Nat.le_refl _) i hi, Nat.mod_eq_of_lt ha]

end VG.Proof.RsaPss.PPC64LE
