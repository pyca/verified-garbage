import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Spec.P256

/-! Arithmetic identities for the P-256 squaring reduction schedule. -/
namespace VG.Proof.Mont.AArch64.P256Square

abbrev B : Nat := 2 ^ 64
abbrev R : Nat := 2 ^ 256
abbrev p : Nat := Spec.P256.curve.p

/-- The shift/subtract schedule forms the four words of `u (p+1)/B`. -/
theorem reduction_words {u lo hi t3 t6 borrow : Nat}
    (hu : u * 2 ^ 32 = lo + B * hi)
    (h3 : t3 + lo = u + B * borrow)
    (h6 : t6 + hi + borrow = u) :
    u * ((p + 1) / B) = lo + B * hi + 2 ^ 128 * t3 + 2 ^ 192 * t6 := by
  have hhigh : t3 + B * t6 = u * (B + 1 - 2 ^ 32) := by
    simp only [B] at *
    omega
  have hsplit : 2 ^ 128 * t3 + 2 ^ 192 * t6 = 2 ^ 128 * (t3 + B * t6) := by
    simp only [B, Nat.mul_add, ← Nat.mul_assoc]
  rw [Nat.add_assoc (lo + B * hi), hsplit, hhigh, ← hu]
  rw [Nat.mul_left_comm, ← Nat.mul_add]
  rfl

/-- One reduction round cancels the low word and stays within four words. -/
theorem reduction_round {t u q r : Nat} (ht : t < R) (hu : u < B)
    (hq : t = u + B * q) (hr : r = q + u * ((p + 1) / B)) :
    B * r = t + u * p ∧ r < R := by
  have hmul : B * ((p + 1) / B) = p + 1 := by decide
  have he : B * r = t + u * p := by
    rw [hr, Nat.mul_add, Nat.mul_left_comm B u, hmul, Nat.mul_add, Nat.mul_one, hq]
    omega
  refine ⟨he,?_⟩
  have hup : u * p ≤ (B - 1) * p := Nat.mul_le_mul_right _ (by omega)
  simp only [B, R, p, Spec.P256.curve, Spec.P256.p] at *
  omega

/-- Four rounds and addition of the original high half give a REDC result. -/
theorem reduction_four {lo hi t1 t2 t3 t4 u0 u1 u2 u3 r : Nat}
    (h0 : B*t1 = lo + u0*p) (h1 : B*t2 = t1 + u1*p)
    (h2 : B*t3 = t2 + u2*p) (h3 : B*t4 = t3 + u3*p)
    (hr : r = t4 + hi) :
    R*r = lo + R*hi + (u0+B*u1+2^128*u2+2^192*u3)*p := by
  rw [hr, Nat.mul_add]
  simp only [Nat.add_mul, B, R, p, Spec.P256.curve, Spec.P256.p] at *
  omega

/-- The unnormalized square lies below twice the modulus. -/
theorem square_redc_bound {a r u : Nat} (ha : a < p) (hu : u < R)
    (he : R*r = a*a + u*p) : r < 2*p := by
  have hpR : p < R := by decide
  have haa : a*a < p*R := Nat.mul_lt_mul'' ha (Nat.lt_trans ha hpR)
  have hup : u*p ≤ (R-1)*p := Nat.mul_le_mul_right p (by omega)
  simp only [R, p, Spec.P256.curve, Spec.P256.p] at *
  omega

end VG.Proof.Mont.AArch64.P256Square
