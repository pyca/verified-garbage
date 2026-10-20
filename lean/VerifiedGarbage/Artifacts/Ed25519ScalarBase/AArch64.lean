module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact AArch64.target {
    notes := ["Uses baseline integer instructions and \
      a comb: the scalar's 64 nibbles n_i give the digits n_i - 8, and digit i's multiple of \
      [16^i]B is an entry of table i, [k 16^i]B for k <= 8, affine, cached as \
      [Y - X, Y + X, 2dT] in the static `VG_ED25519_COMB` and checked against the specification \
      in Lean. Each entry is selected in constant time (reading every entry of its table) and \
      negated under its sign's mask; the 64 additions, and no doublings, run inline on \
      s2n-bignum's `_alt` field operations (`mul_4`, `add_twice4`, `sub_twice4`), operation for \
      operation as in `edwards25519_scalarmulbase_alt`, the accumulator's coordinates below \
      2·(2^255 - 19) between additions. The working values and saved registers reside in \
      `scratch`."]
    consts := Impl.Ed25519.AArch64.combConsts
    code := Impl.Ed25519.AArch64.scalarBase
    verified := Proof.Ed25519.AArch64.scalarBase_verified }]

end VG.Artifacts.Ed25519ScalarBase.AArch64
