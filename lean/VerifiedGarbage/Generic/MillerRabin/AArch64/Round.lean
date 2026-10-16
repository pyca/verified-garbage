module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The shared prepared Miller–Rabin round on AArch64 -/

@[expose] public section

namespace VG.Generic.MillerRabin.AArch64.Round

open VG.AArch64

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  { Spec.MillerRabin.roundApi Spec.MillerRabin.compact with
    name := v.name
    target := target
    doc := (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).doc
      (notes := ["Four-bit windows using RSA's verified Montgomery arithmetic. \
        The round result is returned without branching on it."])
    code := v.code
    contract := Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact
    verified := by exact v.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MillerRabin.AArch64.Round
