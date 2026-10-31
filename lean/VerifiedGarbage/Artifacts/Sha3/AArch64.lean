module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-3 and SHAKE (FIPS 202) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha3.AArch64

def artifacts : List Artifact := [
  Spec.Sha3.permuteApi.artifact AArch64.target {
    suffix := "_sha3"
    code := Impl.Sha3.AArch64.Sha3.Vector.permute
    verified := Proof.Sha3.AArch64.Sha3.Vector.permute_verified
    features := ["sha3"] },
  Spec.Sha3.permuteApi.artifact AArch64.target {
    code := Impl.Sha3.AArch64.Scalar.Lazy.permute
    verified := Proof.Sha3.AArch64.Scalar.Lazy.permute_verified }]

end VG.Artifacts.Sha3.AArch64
