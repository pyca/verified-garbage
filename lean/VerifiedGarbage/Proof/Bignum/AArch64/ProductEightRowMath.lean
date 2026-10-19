module

public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.Proof.Bignum

/-- A slice of a multiword value is bounded by the whole value at its radix. -/
theorem wv_window_le (m : Mem) (B : Addr) (e n i len : Nat) (hi : i + len ≤ n) :
    2 ^ (64 * i) * wv m B (e + 8 * i) len ≤ wv m B e n := by
  have h := wv_add m B e i (len + (n - (i + len)))
  have h' := wv_add m B (e + 8 * i) len (n - (i + len))
  rw [show i + (len + (n - (i + len))) = n by omega, h'] at h
  rw [h, Nat.mul_add]
  omega

theorem row_window_bound {weight window pref operand : Nat}
    (hw : 0 < weight) (hp : pref < weight)
    (hv : weight * window ≤ pref * operand) : window ≤ operand := by
  have h := Nat.le_trans hv (Nat.mul_le_mul_right operand (Nat.le_of_lt hp))
  exact Nat.le_of_mul_le_mul_left h hw

/-- A completed row adds exactly the next eight-limb digit times the multiplier. -/
theorem row_value {before after old new digit operand pref weight : Nat}
    (frame : after + weight * old = before + weight * new)
    (row : new = old + digit * operand)
    (prior : before = pref * operand) :
    after = (pref + weight * digit) * operand := by
  grind

end VG.Proof.Bignum.AArch64.ProductEight
