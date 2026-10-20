module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-!
# The arithmetic schedule used by the DSA implementation

These equalities justify reducing the digest and every scalar intermediate,
and using the shared RSA power routine. They retain all rejection conditions
and require no primality assumption.
-/

@[expose] public section

namespace VG.Proof.Dsa
open VG.Spec.Dsa

/-- The signing core's separately reduced scalar intermediates have exactly
the spec's value. -/
theorem signWithNonce_reduced (key : Key) (digest : List VG.Byte) (k x n : Nat)
    (hx : key.x = some x) (hq : bitLength key.params.q = 8 * n) :
    signWithNonce key digest k =
      if !keyValid key || !(0 < k && k < key.params.q) then none else
        let q := key.params.q
        let r := Spec.Rsa.powMod key.params.g k key.params.p % q
        let inverse := Spec.Rsa.powMod k (q - 2) q
        let z := decodeBE (digest.take n) % q
        let xr := x * r % q
        let s := inverse * ((z + xr) % q) % q
        if r == 0 || s == 0 then none else some ⟨r, s⟩ := by
  unfold signWithNonce
  rw [hx]
  dsimp only
  rw [powMod_rsa, powMod_rsa, digestScalar_prefix _ _ _ hq]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rfl

/-- Verification uses the same digest prefix and may reduce it before
multiplication by the specified Fermat power, including for composite q. -/
theorem verify_reduced (key : Key) (signature : Signature) (digest : List VG.Byte) (n : Nat)
    (hq : bitLength key.params.q = 8 * n) :
    verify key signature digest =
      if !keyValid { key with x := none } ||
          !(0 < signature.r && signature.r < key.params.q &&
            0 < signature.s && signature.s < key.params.q) then false else
        let q := key.params.q
        let inverse := Spec.Rsa.powMod signature.s (q - 2) q
        let z := decodeBE (digest.take n) % q
        let u := z * inverse % q
        let v := signature.r * inverse % q
        (Spec.Rsa.powMod key.params.g u key.params.p *
          Spec.Rsa.powMod key.y v key.params.p % key.params.p) % q == signature.r := by
  unfold verify
  dsimp only
  rw [digestScalar_prefix _ _ _ hq]
  simp only [powMod_rsa, Nat.mod_mul_mod]

end VG.Proof.Dsa
