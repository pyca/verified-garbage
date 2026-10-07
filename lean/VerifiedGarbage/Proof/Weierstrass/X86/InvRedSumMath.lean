import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned

/-! # Appending a sign word after a bounded unsigned product -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Proof.Mont

theorem add_top_mod {A V top sign : Nat} (hA : 0 < A) (hV : V < A) :
    V + A * ((top + sign) % 2 ^ 32) = (V + A * top + A * sign) % (A * 2 ^ 32) := by
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.mod_mul, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hV, Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt hV, Nat.zero_add]

theorem row_bound {m : Mem} {base : Addr} {acc tmp modulus n : Nat}
    (h : val32 m base acc (n + 2) < 2 ^ (32 * (n + 1))) :
    val32 m base acc (n + 2) + w32 m base tmp * val32 m base modulus n < 2 ^ (32 * (n + 2)) := by
  have P := product_bound m base tmp modulus n
  have E : 2 ^ (32 * (n + 2)) = 2 ^ 32 * 2 ^ (32 * (n + 1)) := pow32_succ (n + 1)
  rw [E]
  omega

end VG.Proof.Weierstrass.X86.Inv
