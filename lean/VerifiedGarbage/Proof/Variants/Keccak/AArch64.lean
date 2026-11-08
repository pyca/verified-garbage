module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.ResidentBackend
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.ResidentBackend

/-! # The implementations of `Keccak` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Keccak.AArch64

def scalar : Proof.Sha3.AArch64.Permutation := Proof.Sha3.AArch64.Scalar.Lazy.ResidentBackend.backend

-- FEAT_SHA3's Keccak is faster on Apple's cores, and slower on Neoverse N2.
def sha3 : Proof.Sha3.AArch64.Permutation :=
  { Proof.Sha3.AArch64.Sha3.ResidentBackend.backend with vendor := some "apple" }

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [sha3, scalar]

end VG.Proof.Variants.Keccak.AArch64
