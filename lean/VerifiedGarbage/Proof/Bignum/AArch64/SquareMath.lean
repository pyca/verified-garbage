module

public import VerifiedGarbage.Proof.Bignum.Square
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! Digit identities shared in organization with the x86-64 square proof. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.Proof.Bignum

theorem wv_zero {m : Mem} {B : Addr} {d n : Nat}
    (h : ∀ k < n, word m B (d+8*k) = 0) : wv m B d n = 0 :=
  (wv_eq_zero_iff m B d n).mpr h

/-- Replacing a contiguous digit window changes the whole value by the
window's change times its radix offset. -/
theorem wv_change_window {m m' : Mem} {B : Addr} {A n i len v : Nat}
    (hn : i + len ≤ n) (hA : A + 8 * n ≤ 2 ^ 64)
    (ho : Outside B (A + 8 * i) (8 * len) m m')
    (hv : wv m' B (A + 8 * i) len = wv m B (A + 8 * i) len + v) :
    wv m' B A n = wv m B A n + 2 ^ (64 * i) * v := by
  have hl : wv m' B A i = wv m B A i := ho.wv (by omega) (by omega)
  have hh : wv m' B (A + 8 * i + 8 * len) (n - (i + len)) =
      wv m B (A + 8 * i + 8 * len) (n - (i + len)) := ho.wv (by omega) (by omega)
  have he : n = i + (len + (n - (i + len))) := by omega
  have h1 := wv_add m' B A i (len + (n - (i + len)))
  have h2 := wv_add m B A i (len + (n - (i + len)))
  rw [← he] at h1 h2
  rw [h1, h2, wv_add m' B (A + 8 * i), wv_add m B (A + 8 * i), hl, hh, hv]
  grind

/-- The target-independent digit value agrees with the working-space one. -/
theorem value_words (m : Mem) (B : Addr) (eb i : Nat) :
    VG.Proof.Bignum.Square.value (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i = wv m B eb i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [VG.Proof.Bignum.Square.value, wv, ih, ← Nat.pow_mul, Nat.mul_comm (word m B (eb + 8 * i)).toNat]

/-- The off-diagonal product of the first `i` input words, counted once. -/
def crossValue (m : Mem) (B : Addr) (eb : Nat) (i : Nat) : Nat :=
  VG.Proof.Bignum.Square.cross (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i

theorem crossValue_succ (m : Mem) (B : Addr) (eb i : Nat) :
    crossValue m B eb (i + 1) = crossValue m B eb i +
      wv m B eb i * (word m B (eb + 8 * i)).toNat * 2 ^ (64 * i) := by
  unfold crossValue
  rw [VG.Proof.Bignum.Square.cross, value_words, ← Nat.pow_mul]

theorem crossValue_congr {m m' : Mem} {B : Addr} {eb w : Nat}
    (h : ∀ j < w, word m' B (eb + 8 * j) = word m B (eb + 8 * j)) :
    crossValue m' B eb w = crossValue m B eb w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [crossValue_succ, crossValue_succ, ih (fun j hj => h j (by omega)), h w (by omega),
      wv_congr (fun j hj => h j (by omega))]

def diagonalValue (m : Mem) (B : Addr) (eb i : Nat) : Nat :=
  VG.Proof.Bignum.Square.diagonal (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i

theorem diagonalValue_succ (m : Mem) (B : Addr) (eb i : Nat) :
    diagonalValue m B eb (i + 1) = diagonalValue m B eb i +
      (word m B (eb + 8 * i)).toNat * (word m B (eb + 8 * i)).toNat * 2 ^ (128 * i) := by
  unfold diagonalValue
  rw [VG.Proof.Bignum.Square.diagonal, ← Nat.pow_mul]
  have h : 2 ^ (128 * i) = 2 ^ (64 * i) * 2 ^ (64 * i) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h]
  grind

theorem diagonalValue_congr {m m' : Mem} {B : Addr} {eb w : Nat}
    (h : ∀ j < w, word m' B (eb + 8 * j) = word m B (eb + 8 * j)) :
    diagonalValue m' B eb w = diagonalValue m B eb w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [diagonalValue_succ, diagonalValue_succ, ih (fun j hj => h j (by omega)), h w (by omega)]

theorem square_decomposition (m : Mem) (B : Addr) (eb w : Nat) :
    2 * crossValue m B eb w + diagonalValue m B eb w = wv m B eb w * wv m B eb w := by
  have h := VG.Proof.Bignum.Square.decomposition (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) w
  rw [value_words] at h
  exact (Nat.add_comm _ _).trans h.symm

end VG.Proof.Bignum.AArch64.Square
