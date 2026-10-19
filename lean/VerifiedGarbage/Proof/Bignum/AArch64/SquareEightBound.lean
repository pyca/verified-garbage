module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Bignum.AArch64.SquareEight
import VerifiedGarbage.TCB.AArch64.Simd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64.SquareEight

private theorem cross_succ_bound {r x d c diag p : Nat}
    (hr : 0 < r) (hx : x < p) (hd : d < r) (hc : x*x = diag + 2*c) :
    c + x*d*p < p*p*r := by
  have hc' : c < p*p := by
    have hh := Nat.mul_lt_mul_of_lt_of_lt hx hx
    omega
  have hh : p * (r - 1) + p = p*r := by
    rw [← Nat.mul_succ, show (r - 1).succ = r by omega]
  have hp' : x*d*p ≤ p*(r-1)*p :=
    Nat.mul_le_mul_right p (Nat.mul_le_mul (Nat.le_of_lt hx) (by omega))
  have he : p*p + p*(r-1)*p = p*p*r := by
    calc
      _ = (p + p*(r-1))*p := by grind
      _ = (p*r)*p := by rw [Nat.add_comm, hh]
      _ = _ := by grind
  omega

theorem cross_words_succ_lt (m : Mem) (B : Addr) (e n : Nat) :
    Square.crossValue m B e (n+1) < 2 ^ (64*(2*n+1)) := by
  have hx := wv_lt m B e n
  have hd := (word m B (e + 8*n)).isLt
  have hc := (Square.square_decomposition m B e n).symm
  have h := cross_succ_bound (by decide : 0 < 2 ^ 64) hx hd
    (hc.trans (Nat.add_comm _ _))
  have hp : 2 ^ (64*n) * 2 ^ (64*n) * 2 ^ 64 = 2 ^ (64*(2*n+1)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [Square.crossValue_succ]
  exact Nat.lt_of_lt_of_eq h hp

/-- The highest off-diagonal term of eight limbs is at degree thirteen;
all its accumulated carries fit the fifteenth word. -/
theorem cross_words_lt (m : Mem) (B : Addr) (e : Nat) :
    Square.crossValue m B e 8 < (2 ^ 64) ^ 15 := by
  have hx := wv_lt m B e 7
  have hd := (word m B (e + 8*7)).isLt
  have hc := (Square.square_decomposition m B e 7).symm
  have h := cross_succ_bound (by decide : 0 < 2 ^ 64) hx hd
    (hc.trans (Nat.add_comm _ _))
  rw [Square.crossValue_succ]
  have hp (r : Nat) : r ^ 7 * r ^ 7 * r = r ^ 15 := by
    rw [← Nat.pow_add, ← Nat.pow_succ]
  have hp' := hp (2 ^ 64)
  rw [← Nat.pow_mul] at hp'
  exact Nat.lt_of_lt_of_eq h hp'

end VG.Proof.Bignum.AArch64.SquareEight
