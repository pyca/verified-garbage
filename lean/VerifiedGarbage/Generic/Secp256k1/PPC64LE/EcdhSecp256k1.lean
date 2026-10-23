module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Secp256k1.Lit

/-!
# ECDH over secp256k1 (SP 800-56A §5.7.1.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcdhSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_secp256k1_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves \
      `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), keeps `out` in `r14` and \
      `peer` in `r12`; field elements are four 64-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication (CIOS, in calls of `vg_secp256k1_mul_mod_p` and the other \
      functions of `secp256k1_mont`) with a final conditional subtraction. The peer's key is checked \
      without branches (its first byte, both coordinates below `p`, and the curve's equation), \
      and the ladder multiplies the peer's point if it is valid, else `G`, so it always runs on a \
      point of the curve. `[d]P` is a double-and-add ladder over all 256 bits of `d`, with the \
      complete addition formulas of Renes, Costello and Batina (calls of `vg_secp256k1_point_double` \
      and `vg_secp256k1_point_add`) and a masked selection for each bit; `Z⁻¹` is Fermat's, by \
      square-and-always-multiply. The result (or zeros) is selected by a mask of the checks, \
      `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.Ecdh.PPC64LE.exchangeSecp256k1
    verified := Proof.Ecdh.PPC64LE.Secp256k1.ecdh_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcdhSecp256k1
