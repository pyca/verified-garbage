import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Divstep.Tc32Words

/-! # Truncated products and signed corrections -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Proof.Mont

theorem prefix_mod (m : Mem) (base : Addr) (a k n : Nat) (h : k ≤ n) :
    val32 m base a k = val32 m base a n % 2 ^ (32 * k) := by
  have E := val32_append m base a k (n - k)
  rw [show k + (n - k) = n by omega] at E
  rw [E, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt m base a k)]

theorem shifted_prefix_mod (m : Mem) (base : Addr) (a k n : Nat) (h : k ≤ n) :
    (2 ^ 32 * val32 m base a k) % 2 ^ (32 * (k + 1)) =
      (2 ^ 32 * val32 m base a n) % 2 ^ (32 * (k + 1)) := by
  have E := val32_append m base a k (n - k)
  rw [show k + (n - k) = n by omega] at E
  rw [E]
  have F : 2 ^ 32 * (val32 m base a k + 2 ^ (32 * k) *
      val32 m base (a + 4 * k) (n - k)) =
      2 ^ 32 * val32 m base a k + 2 ^ (32 * (k + 1)) *
        val32 m base (a + 4 * k) (n - k) := by
    rw [pow32_succ]
    ring
  rw [F, Nat.add_mul_mod_self_left]

theorem corrections_mod {R B lo mid fin X Y P c d : Nat}
    (h0 : lo = P % R) (h1 : mid + B * X = lo + R * c) (h2 : fin + B * Y = mid + R * d) :
    (fin + B * (X + Y)) % R = P % R := by
  have E : fin + B * (X + Y) = lo + R * (c + d) := by nlinarith
  rw [E, Nat.add_mul_mod_self_left, h0, Nat.mod_mod]

end VG.Proof.Weierstrass.X86.Inv
