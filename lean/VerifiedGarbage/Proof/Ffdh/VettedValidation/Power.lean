module

public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! Small, kernel-checked blocks of binary exponentiation certify fixed public
subgroup checks without putting primality or a computation oracle in the TCB. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation

/-- Append the low `n` bits of `b` to a binary exponent whose residue is `a`. -/
def powerBlock (p a b : Nat) : Nat → Nat
  | 0 => a % p
  | n + 1 =>
    let r := powerBlock p a (b / 2) n
    (r * r * 2 ^ (b % 2)) % p

theorem powerBlock_correct (p a b n : Nat) :
    powerBlock p a b n = a ^ (2 ^ n) * 2 ^ (b % 2 ^ n) % p := by
  induction n generalizing b with
  | zero => simp only [powerBlock, Nat.pow_zero, Nat.pow_one, Nat.mod_one, Nat.mul_one]
  | succ n ih =>
    rw [powerBlock, ih]
    have bits : b % 2 ^ (n + 1) = 2 * (b / 2 % 2 ^ n) + b % 2 := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mod_mul]
      omega
    rw [bits, Nat.pow_succ, Nat.pow_mul a, Nat.pow_add,
      Nat.mul_comm 2 (b / 2 % 2 ^ n), Nat.pow_mul 2]
    rw [← Nat.mod_mul_mod
      ((a ^ (2 ^ n) * 2 ^ (b / 2 % 2 ^ n) % p) *
        (a ^ (2 ^ n) * 2 ^ (b / 2 % 2 ^ n) % p)) (2 ^ (b % 2)) p,
      ← Nat.mul_mod, Nat.mod_mul_mod]
    congr 1
    simp only [Nat.pow_two]
    ac_rfl

theorem powerBlock_append {p e a b n r : Nat} (previous : 2 ^ e % p = a)
    (fits : b < 2 ^ n) (certificate : powerBlock p a b n = r) :
    2 ^ (e * 2 ^ n + b) % p = r := by
  rw [powerBlock_correct, Nat.mod_eq_of_lt fits] at certificate
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod,
    Nat.pow_mod (2 ^ e), previous, ← Nat.mul_mod]
  exact certificate

end VG.Proof.Ffdh.VettedValidation
