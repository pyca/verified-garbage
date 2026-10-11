import VerifiedGarbage.Spec.Weierstrass.Inverse

/-!
# The contracts of `Spec/Weierstrass/Inverse.lean`

* For P-384's prime `p` and order `n` and a few numbers `x` in Montgomery's
  form (`x R mod m`), the power the contracts state, `dec(x)^(m-2)`, is the
  inverse of `dec(x)` (`dec(x) · dec(x)^(m-2) = 1`), and the Montgomery form
  of `x⁻¹` decodes to it;
* the functions' own working space is where the documentation says, and
  apart from what the caller provides (`p`, `n`, `Z`, `x`) and from the
  result.
-/

namespace VG.Test.WeierstrassInverse

open Spec.Weierstrass Spec.Weierstrass.Inverse

def C : Inverse.Curve := p384

/-- `x R mod m`. -/
def mont (m x : Nat) : Nat := x * 2 ^ (64 * C.k) % m

def values : List Nat := [1, 2, 3, 0x1234567, 2 ^ 383 + 5]

/-- The stated power is the inverse modulo `m`, and is what the Montgomery
form of the inverse decodes to. -/
def checkInv (m : Nat) [NeZero m] : Bool := values.all fun x =>
  let a := C.dec m (mont m x)
  let b := pow a (m - 2)
  a * b = 1 && C.dec m (mont m (pow (Fin.ofNat m x) (m - 2)).val) = b

#guard checkInv C.W.p
#guard checkInv C.W.n

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

#guard p384.ownDoc = "Bytes 1504 to 1551, 4048 to 4095 and 3400 to 3847 of `ws`"
#guard p384.zAt = 832 ∧ p384.xAt = 1840 ∧ p384.outAt = 1456 ∧ p384.pAt = 64 ∧ p384.nAt = 112

end VG.Test.WeierstrassInverse
