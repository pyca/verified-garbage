module

import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-!
# The contracts of `Proof/Weierstrass/InverseContract.lean`

* For every curve's prime `p` and order `n` and a few numbers `x` in Montgomery's
  form (`x R mod m`), the power the contracts state, `dec(x)^(m-2)`, is the
  inverse of `dec(x)` (`dec(x) · dec(x)^(m-2) = 1`), and the Montgomery form
  of `x⁻¹` decodes to it;
* the functions' own working space is apart from what the caller provides (`p`, `n`, `Z`, `x`) and from the
  result.
-/

namespace VG.Test.WeierstrassInverse

open Spec.Weierstrass Impl.Weierstrass.Inverse Impl.Weierstrass

/-- `x R mod m`. -/
def mont (C : Inverse.Curve) (m x : Nat) : Nat := x * 2 ^ (64 * C.k) % m

def values : List Nat := [1, 2, 3, 0x1234567, 2 ^ 383 + 5]

/-- The stated power is the inverse modulo `m`, and is what the Montgomery
form of the inverse decodes to. -/
def checkInv (C : Inverse.Curve) (m : Nat) [NeZero m] : Bool := values.all fun x =>
  let a := C.dec m (mont C m x)
  let b := pow a (m - 2)
  a * b = 1 && C.dec m (mont C m (pow (Fin.ofNat m x) (m - 2)).val) = b

#guard checkInv p384 p384.W.p
#guard checkInv p384 p384.W.n
#guard checkInv p521 p521.W.p
#guard checkInv p521 p521.W.n
#guard checkInv p192 p192.W.p
#guard checkInv p192 p192.W.n
#guard checkInv p224 p224.W.p
#guard checkInv p224 p224.W.n
#guard checkInv p256 p256.W.p
#guard checkInv p256 p256.W.n
#guard checkInv secp256k1 secp256k1.W.p
#guard checkInv secp256k1 secp256k1.W.n

/-- Byte `i` is in the own working space, as a `Bool`. -/
def own (C : Inverse.Curve) (i : Nat) : Bool :=
  (C.slot 30 ≤ i && i < C.slot 31) || (C.tmpAt ≤ i && i < C.tmpAt + 8 * C.k) ||
    (C.workAt ≤ i && i < C.workAt + C.workLen)

theorem own_iff (C : Inverse.Curve) (i : Nat) : own C i = true ↔ C.Own i := by
  simp [own, Curve.Own, or_assoc]

/-- The bytes of what the caller provides, and of the result, are not in the
own working space, which is in `ws`. -/
def checkApart (C : Inverse.Curve) : Bool :=
  (List.range (8 * C.k)).all (fun i => !own C (C.pAt + i) && !own C (C.nAt + i) &&
    !own C (C.zAt + i) && !own C (C.xAt + i) && !own C (C.outAt + i)) &&
    C.workAt + C.workLen ≤ 8192 && C.tmpAt + 8 * C.k ≤ 8192

#guard curves.all checkApart

#guard p384.zAt = 832 ∧ p384.xAt = 1840 ∧ p384.outAt = 1456 ∧ p384.pAt = 64 ∧ p384.nAt = 112
#guard [p192, p224, p256, secp256k1].all fun C =>
  C.zAt == 576 && C.xAt == 1248 && C.outAt == 992 && C.pAt == 64 && C.nAt == 96
#guard p521.zAt = 1216 ∧ p521.xAt = 2728 ∧ p521.outAt = 2152 ∧ p521.pAt = 64 ∧ p521.nAt = 136

end VG.Test.WeierstrassInverse
