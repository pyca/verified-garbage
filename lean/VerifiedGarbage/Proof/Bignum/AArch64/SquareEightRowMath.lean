module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRowMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMath
import Batteries.Tactic.Init

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- A full-buffer value below a digit boundary has a zero window above it. -/
theorem zero_window_of_lt {m : Mem} {B : Addr} {e n i len : Nat}
    (hi : i+len ≤ n) (hv : wv m B e n < 2 ^ (64*i)) :
    wv m B (e+8*i) len = 0 := by
  have hw := ProductEight.wv_window_le m B e n i len hi
  by_contra hz
  have hp := Nat.mul_le_mul_left (2 ^ (64*i)) (show 1 ≤ wv m B (e+8*i) len by omega)
  simp only [Nat.mul_one] at hp
  omega

theorem cross_words_lt_full (m : Mem) (B : Addr) (e n : Nat) :
    Square.crossValue m B e n < 2 ^ (128*n) := by
  have hv := wv_lt m B e n
  have hc := Square.square_decomposition m B e n
  have hp := Nat.mul_lt_mul_of_lt_of_lt hv hv
  have he : 2 ^ (64*n) * 2 ^ (64*n) = 2 ^ (128*n) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [he] at hp
  omega

theorem row_cross_add (m : Mem) (B : Addr) (e i : Nat) :
    Square.crossValue m B e (8*(i+1)) = Square.crossValue m B e (8*i) +
      2 ^ (64*(16*i)) * Square.crossValue m B (e+64*i) 8 +
      2 ^ (64*(8*i)) * (wv m B (e+64*i) 8 * wv m B e (8*i)) := by
  rw [show 8*(i+1) = 8*i+8 by omega, crossValue_add]
  simp only [show 128*(8*i) = 64*(16*i) by omega, show 8*(8*i) = 64*i by omega]
  rw [Nat.mul_assoc, Nat.mul_comm (wv m B e (8*i))]

theorem row_cross_bound (m : Mem) (B : Addr) (e i : Nat) :
    Square.crossValue m B e (8*(i+1)) < 2 ^ (64*(16*i+15)) := by
  have h := cross_words_succ_lt m B e (8*i+7)
  simpa only [show 8*i+7+1 = 8*(i+1) by omega,
    show 2*(8*i+7)+1 = 16*i+15 by omega] using h

end VG.Proof.Bignum.AArch64.SquareEight
