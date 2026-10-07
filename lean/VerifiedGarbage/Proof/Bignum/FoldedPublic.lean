import VerifiedGarbage.Proof.Bignum.Math

/-! The last multiplication of a public exponentiation also leaves Montgomery form. -/
namespace VG.Proof.Bignum

/-- Fold an arbitrary ordinary factor into the conversion out of Montgomery form. -/
theorem mont_final_factor {Y out x u e R m : Nat} (hR : Nat.Coprime R m)
    (hY : Y % m = x^e * R % m)
    (h : out * R % m = Y * u % m) :
    out % m = x^e * u % m := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod Y, hY, ← Nat.mul_mod]
  congr 1
  ac_rfl

/-- Recover the ordinary base from a valid cached Montgomery conversion. -/
theorem encoded_base {Y x u RR R N : Nat} (hR : Nat.Coprime R N)
    (hx : Y % N = x * R % N) (hm : Y * R % N = u * RR % N)
    (hRR : RR % N = R * R % N) : x % N = u % N := by
  apply mont_cancel hR
  apply mont_cancel hR
  calc x * R * R % N = x * R % N * R % N := (Nat.mod_mul_mod _ _ _).symm
    _ = Y % N * R % N := by rw [hx]
    _ = u * RR % N := by rw [Nat.mod_mul_mod,hm]
    _ = u * (RR % N) % N := (Nat.mul_mod_mod _ _ _).symm
    _ = u * R * R % N := by rw [hRR,Nat.mul_mod_mod,Nat.mul_assoc]

theorem factor_congr {x u e N : Nat} (h : x % N = u % N) :
    x^e * u % N = u^(e+1) % N := by
  rw [Nat.mul_mod,Nat.pow_mod,h,← Nat.pow_mod,← Nat.mul_mod,← Nat.pow_succ]

/-- Multiplication by the ordinary input, instead of its Montgomery encoding,
combines the final exponent bit with the conversion out of Montgomery form. -/
theorem mont_final_input {Y out x e R m : Nat} (hR : Nat.Coprime R m)
    (hY : Y % m = x ^ e * R % m)
    (h : out * R % m = Y * x % m) :
    out % m = x ^ (e + 1) % m := by
  apply mont_cancel hR
  rw [h, Nat.mul_mod Y, hY, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  ac_rfl

end VG.Proof.Bignum
