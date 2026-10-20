module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The shared prepared Miller–Rabin round on AArch64 -/

@[expose] public section

namespace VG.Generic.MillerRabin.AArch64.Round

open VG.AArch64

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact target {
    suffix := v.suffix
    notes := ["Four-bit windows using RSA's verified Montgomery arithmetic. \
        The round result is returned without branching on it."]
    code := v.code
    verified := v.verified
    features := v.features }]

end VG.Generic.MillerRabin.AArch64.Round
