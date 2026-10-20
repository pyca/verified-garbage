module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The shared prepared Miller–Rabin round on ARMv7 -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.Round

open VG.Arm

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).artifact target {
    suffix := v.suffix
    notes := ["ARMv7: fixed windows of four bits, by `vg_rsa_public_checked`'s Montgomery multiplication \
        on 32-bit limbs, and a dedicated Montgomery square for the squarings (each cross product \
        once, doubled, the words' squares added, then reduced in place). The table of the 16 powers is built once (14 products, the entries shifted \
        down one a product); each window squares four times, or'ing the flag with `y = −1` under \
        masks, selects its entry by a scan of all 16 under masks into array 5, multiplies, and sets \
        the flag under the mask of a nonzero digit. Three last squarings use the threshold `4 − σ` \
        from the word after the exponent. The round result is returned without branching on it."]
    code := v.code
    stack := 56
    verified := v.verifiedSpec
    features := v.features }]

end VG.Generic.MillerRabin.Arm.Round
