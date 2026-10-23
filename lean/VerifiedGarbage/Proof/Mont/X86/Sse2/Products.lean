module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Dot
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Framework.Omega

/-! # A column's products as coefficients

`dot` sums the products of the words at the same index of two numbers
(`dsum`). One of the two is a number stored in reverse (`A'` and the
quotient digits `Q'`), so the sum is a column's `Σ f_i g_(k-i)` over a range
of `i` (`dsum_rev`, `csum`), which is the column's coefficient of a product
(`csum_product`), of a square's products above the diagonal (`csum_cross`),
and of the quotient digits written so far times the modulus
(`csum_reduce`). Each sum is `2³²` times the sum of the products' high words
plus that of their low words (`dsum_split`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.NatSum

/-- The words of a number at offset `x` of the working space. -/
def digits (m : Mem) (W : Addr) (x : Nat) (i : Nat) : Nat := w32 m W (x + 4 * i)

/-- `Σ f_i g_(k-i)` for `i0 ≤ i < i0 + n`. -/
def csum (f g : Nat → Nat) (k i0 n : Nat) : Nat := sum (fun j => f (i0 + j) * g (k - (i0 + j))) n

theorem rsum_eq_sum (f : Nat → Nat) (a n : Nat) : rsum f a n = sum (fun j => f (a + j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rsum, NatSum.succ, ih]

theorem sum_shift (g : Nat → Nat) (n : Nat) : sum g (n + 1) = g 0 + sum (fun j => g (j + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [NatSum.succ, ih, NatSum.succ]; omega

theorem sum_rev (f : Nat → Nat) (n : Nat) : sum f n = sum (fun j => f (n - 1 - j)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [NatSum.succ, ih, sum_shift]
    rw [show (n + 1 - 1 - 0) = n by omega, Nat.add_comm]
    congr 1
    apply NatSum.congr
    intro j hj
    congr 1; omega

/-- A sum of products of two numbers, one stored in reverse: the word `N - 1 - i`
of `xp` is `f_i` for `i0 ≤ i < e`. -/
theorem dsum_rev (m : Mem) (W : Addr) (xp y : Nat) (f : Nat → Nat) {N k e i0 : Nat} (he : e ≤ N)
    (hek : e ≤ k + 1) (hi : i0 ≤ e) (hf : ∀ i, i0 ≤ i → i < e → w32 m W (xp + 4 * (N - 1 - i)) = f i) :
    dsum m W (xp + 4 * (N - e)) (y + 4 * (k + 1 - e)) (e - i0) = csum f (digits m W y) k i0 (e - i0) := by
  rw [dsum, rsum_eq_sum, sum_rev, csum]
  apply NatSum.congr
  intro j hj
  simp only [Nat.zero_add, dprod, digits]
  rw [show xp + 4 * (N - e) + 4 * (e - i0 - 1 - j) = xp + 4 * (N - 1 - (i0 + j)) by omega,
    show y + 4 * (k + 1 - e) + 4 * (e - i0 - 1 - j) = y + 4 * (k - (i0 + j)) by omega,
    hf (i0 + j) (by omega) (by omega)]

theorem csum_product (f g : Nat → Nat) {N k : Nat} :
    csum f g k (k + 1 - N) (min (k + 1) N - (k + 1 - N)) = Column.coeff f g N k := by
  rw [csum, Column.coeff_range, ← interval (fun i => f i * g (k - i)) N (k + 1 - N)
    (min (k + 1) N) (Nat.min_le_right _ _)]
  apply NatSum.congr
  intro i hi
  have e : (i ≤ k ∧ k - i < N) ↔ (k + 1 - N ≤ i ∧ i < min (k + 1) N) := by omega
  simp only [e]

theorem csum_cross (f : Nat → Nat) {N k : Nat} (hk : k < 2 * N) :
    csum f f k (k + 1 - N) ((k + 1) / 2 - (k + 1 - N)) = Column.crossCoeff f N k := by
  rw [csum, Column.crossCoeff_scan _ hk]

theorem csum_reduce (q g : Nat → Nat) {N k : Nat} :
    csum q g k (k + 1 - N) (min k N - (k + 1 - N)) = Column.coeff (Column.prefixDigits q k) g N k := by
  rw [csum, Column.coeff_prefix_scan]

/-- The last two terms of a column's sum from `0`. -/
theorem csum_two (q g : Nat → Nat) {k : Nat} (hk : 2 ≤ k) :
    csum q g k 0 k = csum q g k 0 (k - 2) + q (k - 2) * g 2 + q (k - 1) * g 1 := by
  rw [show k = (k - 2) + 1 + 1 by omega]
  simp only [csum, NatSum.succ, Nat.zero_add]
  rw [show k - 2 + 1 + 1 - 2 = k - 2 by omega, show k - 2 + 1 + 1 - (k - 2) = 2 by omega,
    show k - 2 + 1 + 1 - (k - 2 + 1) = 1 by omega, show k - 2 + 1 = k - 2 + 1 from rfl]
  rw [show k - 2 + 1 + 1 - 1 = k - 2 + 1 by omega]

theorem csum_reduce0 (q g : Nat → Nat) {N k : Nat} (hk : k < N) :
    csum q g k 0 k = Column.coeff (Column.prefixDigits q k) g N k := by
  have := csum_reduce q g (N := N) (k := k)
  rwa [show k + 1 - N = 0 by omega, show min k N - 0 = k by omega] at this

/-- The products' low words. -/
def dlow (m : Mem) (W : Addr) (x y n : Nat) : Nat := rsum (fun j => dprod m W x y j % 2 ^ 32) 0 n

theorem dsum_split (m : Mem) (W : Addr) (x y n : Nat) :
    dsum m W x y n = 2 ^ 32 * dhigh m W x y n + dlow m W x y n ∧ dlow m W x y n ≤ n * (2 ^ 32 - 1) := by
  induction n with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ n ih =>
    have := Nat.div_add_mod (dprod m W x y n) (2 ^ 32)
    have := Nat.mod_lt (dprod m W x y n) (show 0 < 2 ^ 32 by decide)
    simp only [dsum, dhigh, dlow, rsum, Nat.zero_add] at ih ⊢
    rw [Nat.succ_mul]
    constructor <;> omega

end VG.Proof.Mont.X86.Sse2
