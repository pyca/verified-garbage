module

public import VerifiedGarbage.Proof.Bignum.Square
public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint

/-! Arithmetic invariants for a register block of Montgomery multiply-adds.
Low and high product halves use separate carry chains, as in the x86-64
register-blocked arithmetic, but the AArch64 implementation serializes them.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG.Proof.Bignum.Square

theorem value_congr {r n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    value r f n = value r g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, value, h n (by omega), ih (fun i hi => h i (by omega))]


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


/-- Re-express a block after its low digit is emitted. -/
theorem value_shift (r : Nat) (f : Nat → Nat) (n : Nat) :
    f 0 + r * value r (fun i => f (i + 1)) n = value r f (n + 1) := by
  induction n with
  | zero => simp only [value, Nat.pow_zero, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    simp only [value, Nat.pow_succ]
    simp only [value] at ih
    grind

/-- A full block product plus two bounded accumulator blocks cannot overflow
its two-block result. This justifies discarding the high-chain flag after
all eight rows, without assuming that the Montgomery inverse is valid. -/
theorem tile_carry_zero {r a x q n lo hi c : Nat}
    (hr : 1 < r) (ha : a < r) (hx : x < r) (hq : q < r) (hn : n < r)
    (hv : lo + r * (hi + r * c) = a + x + q * n) : c = 0 := by
  have hq' : q ≤ r - 1 := by omega
  have hn' : n ≤ r - 1 := by omega
  have hp := Nat.mul_le_mul hq' hn'
  have he : r * r = (r - 1) * (r - 1) + 2 * (r - 1) + 1 := by
    have h : r = (r - 1) + 1 := by omega
    calc
      r * r = ((r - 1) + 1) * ((r - 1) + 1) := congrArg (fun v => v * v) h
      _ = (r - 1) * (r - 1) + 2 * (r - 1) + 1 := by grind
  have ht : a + x + q * n < r * r := by omega
  by_contra hc
  have hc' : 1 ≤ c := by omega
  have hm := Nat.mul_le_mul_left (r * r) hc'
  simp only [Nat.mul_one] at hm
  rw [Nat.mul_add, ← Nat.mul_assoc] at hv
  omega


/-- Combine the two carry chains and the shift without losing either carry. -/
theorem chained_row_value {b r a q n low high aLow cLow shifted aHigh cHigh cin lo : Nat}
    (hlow : aLow + r * cLow = a + low)
    (hshift : lo + b * shifted = aLow + r * (cin + cLow))
    (hhigh : aHigh + r * cHigh = shifted + high)
    (hprod : low + b * high = q * n) :
    lo + b * (aHigh + r * cHigh) = a + q * n + r * cin := by
  grind

/-- A block of bounded digits is smaller than its radix power. -/
theorem value_lt (r : Nat) (f : Nat → Nat) (k : Nat)
    (hf : ∀ i < k, f i < r) : value r f k < r ^ k := by
  induction k with
  | zero => simp only [value, Nat.pow_zero]; omega
  | succ k ih =>
    have hp := ih (fun i hi => hf i (by omega))
    have hd : f k + 1 ≤ r := by have := hf k (by omega); omega
    calc
      value r f (k + 1) = value r f k + f k * r ^ k := rfl
      _ < r ^ k + f k * r ^ k := Nat.add_lt_add_right hp _
      _ = (f k + 1) * r ^ k := by grind
      _ ≤ r * r ^ k := Nat.mul_le_mul_right _ hd
      _ = r ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- A cancellation row has no incoming carry. Its quotient fits the
register block even if the supplied Montgomery inverse is malformed. -/
theorem cancel_carry_zero {b r a q n lo hi c : Nat}
    (hb : 0 < b) (ha : a < r) (hq : q < b) (hn : n < r)
    (hv : lo + b * (hi + r * c) = a + q * n) : c = 0 := by
  have hq' : q + 1 ≤ b := by omega
  have hn' : n ≤ r - 1 := by omega
  have hp := Nat.mul_le_mul_left q hn'
  have hprod := Nat.mul_le_mul_right (r - 1) hq'
  have he : b * r = b * (r - 1) + b := by
    have hr : r = (r - 1) + 1 := by omega
    calc
      b * r = b * ((r - 1) + 1) := congrArg (b * ·) hr
      _ = b * (r - 1) + b := by rw [Nat.mul_add, Nat.mul_one]
  have ht : a + q * n < b * r := by
    rw [Nat.add_mul, Nat.one_mul] at hprod
    omega
  by_contra hc
  have hm := Nat.mul_le_mul_left (b * r) (show 1 ≤ c by omega)
  simp only [Nat.mul_one] at hm
  rw [Nat.mul_add, ← Nat.mul_assoc] at hv
  omega

/-- Extend the accumulated block equation by one emitted digit. -/
theorem rows_step {b p out state next initial qsum q n lo : Nat}
    (hp : out + p * state = initial + qsum * n)
    (hr : lo + b * next = state + q * n) :
    (out + p * lo) + (p * b) * next = initial + (qsum + p * q) * n := by
  have hs := congrArg (p * ·) hr
  grind

/-- Extend a canceled prefix while retaining its coefficients. -/
theorem cancel_step {b p state next initial qsum q n : Nat}
    (hp : p * state = initial + qsum * n)
    (hr : b * next = state + q * n) :
    (p * b) * next = initial + (qsum + p * q) * n := by
  have hs := congrArg (p * ·) hr
  grind

theorem zero_carry_value {r out acc c rhs : Nat} (hc : c = 0)
    (hv : out + r * (acc + r * c) = rhs) : out + r * acc = rhs := by
  subst c
  simpa only [Nat.mul_zero, Nat.add_zero] using hv

theorem columns_step {r p out acc next initial input modulus q lo x n : Nat}
    (hp : out + p * acc = initial + input + q * modulus)
    (hr : lo + r * next = acc + x + q * n) :
    (out + p * lo) + (p * r) * next =
      initial + (input + p * x) + q * (modulus + p * n) := by
  have hs := congrArg (p * ·) hr
  grind

theorem columns_initial (a q : Nat) : 0 + 1 * a = a + 0 + q * 0 := by
  simp only [Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero]

/-- Combine cancellation, the middle columns, and the pending-carry column
into one complete blocked Montgomery row. -/
theorem block_row_value {r p q a0 ac mid af last inputMid inputLast n0 nMid oldCarry carry : Nat}
    (hC : r * ac = a0 + q * n0)
    (hM : mid + p * af = ac + inputMid + q * nMid)
    (hF : last + r * carry = af + inputLast + oldCarry) :
    r * ((mid + p * last) + (r * p) * carry) =
      (a0 + r * (inputMid + p * inputLast)) + q * (n0 + r * nMid) +
        (r * p) * oldCarry := by
  have hm := congrArg (r * ·) hM
  have hf := congrArg ((r * p) * ·) hF
  grind

theorem row_extend {r w lo hi q n p p' tail : Nat}
    (h : r * (lo + w * p') = hi + q * n + w * p) :
    r * ((lo + w * tail) + w * p') = (hi + (w * r) * tail) + q * n + w * p := by
  grind

theorem append_digit_bound {r p q d : Nat} (hq : q < p) (hd : d < r) :
    q + p * d < p * r := by
  have hr : r = (r - 1) + 1 := by omega
  have hh := Nat.mul_le_mul_left p (show d ≤ r - 1 by omega)
  have hp : p * r = p * (r - 1) + p :=
    (congrArg (p * ·) hr).trans (by rw [Nat.mul_add, Nat.mul_one])
  omega

theorem outer_initial {v raw w c n : Nat} (hv : v = raw) (hc : c = 0) :
    1 * (v + w * c) = raw + 0 * n := by
  rw [hv, hc]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.one_mul, Nat.zero_mul]

end VG.Proof.Bignum.AArch64.BlockedRedc
