module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP384r1.Lit

/-!
# ECDH over brainpoolP384r1 (SP 800-56A §5.7.1.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law `h`, the variant
`Variants/BrainpoolP384r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcdhBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP384r1.exchangeApi.artifact PPC64LE.target {
    notes := ["The function is `vg_ecdsa_brainpoolp384r1_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves \
      `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), keeps `out` in `r14` and \
      `peer` in `r12`; field elements are six 64-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication (CIOS, in calls of `vg_brainpoolp384r1_mul_mod_p` and the other \
      functions of `brainpoolp384r1_mont`) with a final conditional subtraction. The peer's key is checked \
      without branches (its first byte, both coordinates below `p`, and the curve's equation), \
      and the ladder multiplies the peer's point if it is valid, else `G`, so it always runs on a \
      point of the curve. `[d]P` is a double-and-add ladder over all 384 bits of `d`, with the \
      complete addition formulas of Renes, Costello and Batina (calls of `vg_brainpoolp384r1_point_double` \
      and `vg_brainpoolp384r1_point_add`) and a masked selection for each bit; `Z⁻¹` is Fermat's, by \
      square-and-always-multiply. The result (or zeros) is selected by a mask of the checks, \
      `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP384r1
    verified := Proof.Ecdh.PPC64LE.BrainpoolP384r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP384r1.PPC64LE.EcdhBrainpoolP384r1
