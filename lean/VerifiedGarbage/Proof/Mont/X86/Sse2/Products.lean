module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Dot
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Framework.Omega

/-! # A column's products as coefficients

The sums `dot` adds are the column's coefficients (`Column.coeff`): of a
product of two numbers (`lowSum_product`), of a square's products above the
diagonal (`lowSum_cross`), and of the quotient digits written so far times
the modulus (`lowSum_reduce`). Each sum is `2³²` times the sum of the
products' high words plus that of their low words (`lowSum_split`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.NatSum

/-- The words of a number at offset `x` of the working space. -/
def digits (m : Mem) (W : Addr) (x : Nat) (i : Nat) : Nat := w32 m W (x + 4 * i)

theorem rsum_eq_sum (f : Nat → Nat) (a n : Nat) : rsum f a n = sum (fun j => f (a + j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rsum, sum, ih]

theorem lowSum_eq (m : Mem) (W : Addr) (x y k i0 n : Nat) :
    lowSum m W x y k i0 n = sum (fun j => digits m W x (i0 + j) * digits m W y (k - (i0 + j))) n :=
  rsum_eq_sum _ _ _

/-- The products' low words. -/
def lowMod (m : Mem) (W : Addr) (x y k i0 n : Nat) : Nat := rsum (fun i => prod m W x y k i % 2 ^ 32) i0 n

theorem lowSum_split (m : Mem) (W : Addr) (x y k i0 n : Nat) :
    lowSum m W x y k i0 n = 2 ^ 32 * highSum m W x y k i0 n + lowMod m W x y k i0 n ∧
      lowMod m W x y k i0 n ≤ n * (2 ^ 32 - 1) := by
  induction n with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ n ih =>
    have := Nat.div_add_mod (prod m W x y k (i0 + n)) (2 ^ 32)
    have := Nat.mod_lt (prod m W x y k (i0 + n)) (show 0 < 2 ^ 32 by decide)
    simp only [lowSum, highSum, lowMod, rsum] at ih ⊢
    rw [Nat.succ_mul]
    constructor <;> omega

theorem lowSum_product (m : Mem) (W : Addr) (a b : Nat) {N k : Nat} :
    lowSum m W a b k (k + 1 - N) (min (k + 1) N - (k + 1 - N)) =
      Column.coeff (digits m W a) (digits m W b) N k := by
  rw [lowSum_eq, Column.coeff_range, ← interval (fun i => digits m W a i * digits m W b (k - i)) N (k + 1 - N)
    (min (k + 1) N) (Nat.min_le_right _ _)]
  apply NatSum.congr
  intro i hi
  have e : (i ≤ k ∧ k - i < N) ↔ (k + 1 - N ≤ i ∧ i < min (k + 1) N) := by omega
  simp only [e]

theorem lowSum_cross (m : Mem) (W : Addr) (a : Nat) {N k : Nat} (hk : k < 2 * N) :
    lowSum m W a a k (k + 1 - N) ((k + 1) / 2 - (k + 1 - N)) = Column.crossCoeff (digits m W a) N k := by
  rw [lowSum_eq, Column.crossCoeff_scan _ hk]

theorem lowSum_reduce (m : Mem) (W : Addr) (q mo : Nat) {N k : Nat} :
    lowSum m W q mo k (k + 1 - N) (min k N - (k + 1 - N)) =
      Column.coeff (Column.prefixDigits (digits m W q) k) (digits m W mo) N k := by
  rw [lowSum_eq, Column.coeff_prefix_scan]

end VG.Proof.Mont.X86.Sse2
