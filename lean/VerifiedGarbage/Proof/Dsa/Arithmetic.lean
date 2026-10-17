module

public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Bignum.Math

/-!
# DSA's arithmetic and the shared RSA arithmetic

These identities require no primality assumption. In particular, the
exponent q - 2 denotes the specified power even for composite q; none of
these lemmas treats it as a multiplicative inverse.
-/

@[expose] public section

namespace VG.Proof.Dsa

/-- DSA and RSA use exactly the same modular exponentiation. -/
theorem powMod_rsa (a e m : Nat) :
    Spec.Dsa.powMod a e m = Spec.Rsa.powMod a e m := by
  induction e using Nat.strongRecOn with
  | _ e ih =>
    rw [Spec.Dsa.powMod, Spec.Rsa.powMod]
    split
    · rfl
    · rename_i he
      rw [ih (e / 2) (by omega)]

/-- The shared Montgomery exponentiation proofs apply to DSA. -/
theorem powMod_eq (a e m : Nat) : Spec.Dsa.powMod a e m = a ^ e % m := by
  rw [powMod_rsa, VG.Proof.Bignum.powMod_eq]

/-- A modular power is reduced for every nonzero modulus. -/
theorem powMod_lt (a e : Nat) {m : Nat} (hm : 0 < m) :
    Spec.Dsa.powMod a e m < m := by
  rw [powMod_eq]
  exact Nat.mod_lt _ hm

/-- The two byte decoders agree, including leading-zero padding. -/
theorem decodeBE_os2ip (bytes : List VG.Byte) :
    Spec.Dsa.decodeBE bytes = Spec.Rsa.os2ip bytes := rfl

/-- Streaming reduction of a big-endian string. The initial residue need
not already be reduced; the final reduction also covers an empty string. -/
def reduceBytes (m acc : Nat) (bytes : List VG.Byte) : Nat :=
  (bytes.foldl (fun r b => (256 * r + b.toNat) % m) acc) % m

private theorem reduceBytes_fold (m acc : Nat) (bytes : List VG.Byte) :
    reduceBytes m acc bytes =
      (bytes.foldl (fun r b => 256 * r + b.toNat) acc) % m := by
  induction bytes generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [reduceBytes, List.foldl_cons] at *
    rw [ih]
    have hfold (x y : Nat) (hxy : x % m = y % m) :
        (bs.foldl (fun r b => 256 * r + b.toNat) x) % m =
          (bs.foldl (fun r b => 256 * r + b.toNat) y) % m := by
      clear ih
      induction bs generalizing x y with
      | nil => exact hxy
      | cons c cs ih =>
        simp only [List.foldl_cons]
        apply ih
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, hxy]
    exact hfold _ _ (Nat.mod_mod _ _)

/-- Reducing bytes is OS2IP modulo m, rather than a truncation to a word. -/
theorem reduceBytes_eq (m : Nat) (bytes : List VG.Byte) :
    reduceBytes m 0 bytes = Spec.Dsa.decodeBE bytes % m :=
  reduceBytes_fold m 0 bytes

/-- An implementation may reduce each operand and intermediate separately
when computing s. This is valid for composite q as well as prime q. -/
theorem sign_residues (q ki z x r : Nat) :
    (ki % q * ((z % q + (x % q * r % q) % q) % q)) % q =
      ki * (z + x * r) % q := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The two ordinary products in verification may use reduced operands. -/
theorem verify_residues (q a b : Nat) :
    (a % q * (b % q)) % q = a * b % q := by
  exact (Nat.mul_mod a b q).symm

/-- Multiplication by cR in Montgomery arithmetic scales an ordinary
residue by c. Only coprimality of R and m is needed. -/
theorem mont_scale {out input c R m : Nat} (hR : Nat.Coprime R m)
    (h : out * R % m = input * (c * R % m) % m) :
    out % m = input * c % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h]
  simp only [Nat.mul_mod, Nat.mod_mod, Nat.mul_assoc]

/-- Multiplication of two Montgomery-encoded values, without primality. -/
theorem mont_product {out A B a b R m : Nat} (hR : Nat.Coprime R m)
    (hA : A % m = a * R % m) (hB : B % m = b * R % m)
    (h : out * R % m = A * B % m) : out % m = a * b * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  calc
    out * R % m = A * B % m := h
    _ = (a * R) * (b * R) % m := by
      rw [Nat.mul_mod A B, hA, hB, ← Nat.mul_mod]
    _ = (a * b * R) * R % m := by ac_rfl

/-- Multiplication by ordinary one decodes a Montgomery value. -/
theorem mont_decode {out A a R m : Nat} (hR : Nat.Coprime R m)
    (hA : A % m = a * R % m) (h : out * R % m = A * 1 % m) :
    out % m = a % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_one, hA]

end VG.Proof.Dsa
