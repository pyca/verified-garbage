module
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! # A reciprocal estimate needs at most one correction

Trial division reduces a short chunk at a time. Multiplying by floor(2^32/p)
replaces a machine division; its high word underestimates the quotient by
at most one whenever the dividend fits in one word.
-/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation

theorem reciprocal_remainder {B p x : Nat} (hB : 0 < B) (hp : 0 < p) (hx : x < B) :
    let q := x * (B / p) / B
    q * p ≤ x ∧ x - q * p < 2 * p := by
  dsimp only
  let m := B / p
  let q := x * m / B
  have lo := Nat.div_mul_le_self (x * m) B
  have hi := Nat.lt_mul_div_succ (x * m) hB
  have lower : q * p ≤ x := by
    have product : (q * p) * B ≤ x * B := calc
      (q * p) * B = (q * B) * p := by ac_rfl
      _ ≤ (x * m) * p := Nat.mul_le_mul_right p lo
      _ = x * (m * p) := by rw [Nat.mul_assoc]
      _ ≤ x * B := Nat.mul_le_mul_left x (Nat.div_mul_le_self B p)
    exact Nat.le_of_mul_le_mul_right product hB
  refine ⟨lower, ?_⟩
  have he := Nat.mod_lt B hp
  have hxe : x * (B % p) < B * p := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt he) hp
  have product : x * B < ((q + 2) * p) * B := calc
    x * B = (x * m) * p + x * (B % p) := by
      conv => lhs; rw [← Nat.mod_add_div B p, Nat.mul_add]
      dsimp [m]
      ac_rfl
    _ < (B * (q + 1)) * p + B * p := Nat.add_lt_add (Nat.mul_lt_mul_of_pos_right hi hp) hxe
    _ = ((q + 2) * p) * B := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.two_mul]
      ac_rfl
  have upper : x < (q + 2) * p := Nat.lt_of_mul_lt_mul_right product
  rw [Nat.add_mul] at upper
  change x - q * p < 2 * p
  omega

theorem reciprocal_mod {B p x : Nat} (hB : 0 < B) (hp : 0 < p) (hx : x < B) :
    let r := x - x * (B / p) / B * p
    (if r < p then r else r - p) = x % p := by
  obtain ⟨lo, hi⟩ := reciprocal_remainder hB hp hx
  dsimp only at lo hi ⊢
  have eq : x = x * (B / p) / B * p + (x - x * (B / p) / B * p) := (Nat.add_sub_of_le lo).symm
  conv => rhs; rw [eq, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
  split
  · exact (Nat.mod_eq_of_lt ‹_›).symm
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
end VG.Proof.Dsa.X86.Generation
