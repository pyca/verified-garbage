module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ResidentBackend
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

namespace VG.Variants.Keccak.AArch64.Scalar

def variant : Proof.Sha3.AArch64.Permutation := Proof.Sha3.AArch64.Scalar.ResidentBackend.backend

end VG.Variants.Keccak.AArch64.Scalar
