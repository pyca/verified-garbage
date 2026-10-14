module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The shared prepared Miller–Rabin round on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MillerRabin.AArch64

open VG.AArch64

def artifacts : List Artifact := [
  { Spec.MillerRabin.roundApi Spec.MillerRabin.compact with
    target := target
    doc := (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).doc
      (notes := ["Four-bit windows using RSA's verified Montgomery arithmetic. \
        The round result is returned without branching on it."])
    code := Impl.MillerRabin.AArch64.round Proof.Bignum.AArch64.Mont.base.mm
    contract := Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact
    verified := Proof.MillerRabin.AArch64.round_verified Proof.Bignum.AArch64.Mont.base
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MillerRabin.AArch64
