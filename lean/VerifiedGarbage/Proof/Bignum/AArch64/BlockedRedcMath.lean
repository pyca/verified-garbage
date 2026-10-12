import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcMath
import VerifiedGarbage.Proof.Bignum.Square
import VerifiedGarbage.Proof.Ed25519.Word64

/-! Arithmetic invariants for a register block of Montgomery multiply-adds.
Low and high product halves use separate carry chains, as in the x86-64
register-blocked arithmetic, but the AArch64 implementation serializes them.
-/
namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG.Proof.Bignum.Square

theorem value_congr {r n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    value r f n = value r g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, value, h n (by omega), ih (fun i hi => h i (by omega))]

/-- Splitting every word product commutes with assembling the whole block. -/
theorem product_halves (r q : Nat) (f : Nat → Nat) (n : Nat) :
    value r (fun i => q * f i % r) n +
      r * value r (fun i => q * f i / r) n = q * value r f n := by
  induction n with
  | zero => simp only [value, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have h := Nat.mod_add_div (q * f n) r
    simp only [value]
    grind

/-- A row emits its low word and retains the rest in the register block and
carry. Both carry chains are included; no discarded carry is assumed zero. -/
theorem row_value {r k a q n low high lo cLow hi cHigh carry : Nat}
    (hk : 1 ≤ k)
    (hprod : low + r * high = q * n)
    (hlow : lo + r ^ k * cLow = a + low)
    (hhigh : hi + r ^ k * cHigh = lo / r + high + r ^ (k - 1) * (carry + cLow)) :
    lo % r + r * (hi + r ^ k * cHigh) = a + q * n + r ^ k * carry := by
  have hsplit := Nat.mod_add_div lo r
  have hp : r ^ k = r * r ^ (k - 1) := by
    calc
      r ^ k = r ^ ((k - 1) + 1) := congrArg (r ^ ·) (by omega)
      _ = r ^ (k - 1) * r := Nat.pow_succ r (k - 1)
      _ = r * r ^ (k - 1) := Nat.mul_comm _ _
  rw [hhigh]
  grind


open VG.Proof.Ed25519.Word64

/-- Carry entering word `i` of an ordinary scalar carry chain. -/
def chainCarry (a b : Nat → Word) (c : Bool) : Nat → Bool
  | 0 => c
  | i + 1 => carryOut (a i) (b i) (chainCarry a b c i)

/-- Conservation of the entire chain, including both boundary carries. -/
theorem chain_value (a b : Nat → Word) (c : Bool) (n : Nat) :
    value (2 ^ 64) (fun i => (addCarry (a i) (b i) (chainCarry a b c i)).toNat) n +
      (2 ^ 64) ^ n * (chainCarry a b c n).toNat =
      value (2 ^ 64) (fun i => (a i).toNat) n +
        value (2 ^ 64) (fun i => (b i).toNat) n + c.toNat := by
  induction n with
  | zero => simp only [value, chainCarry, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | succ n ih =>
    have h := addCarry_value (a n) (b n) (chainCarry a b c n)
    simp only [value, chainCarry, Nat.pow_succ]
    grind

end VG.Proof.Bignum.AArch64.BlockedRedc
