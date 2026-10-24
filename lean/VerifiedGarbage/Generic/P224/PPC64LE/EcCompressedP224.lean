module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit

/-!
# P-224 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/PPC64LE/Law.lean`, which decompression's proof of its square
root uses.
-/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcCompressedP224

/-- How the functions work. -/
def notes : List String := ["The functions are `vg_ecdh_p224`'s setup, field arithmetic and checks: they save `r14`, `r31` \
  and `lr` in `scratch` (in `r3` during the function), keep `out` in `r14` and `public` in `r12` \
  while they read it; field elements are four 64-bit words in Montgomery form, multiplied by calls \
  of `vg_p224_mul_mod_p` and the other functions of `p224_mont`. Compression checks the key as \
  ECDH checks the peer's (its first byte, both coordinates below `p` and the curve's equation) and \
  writes the tag from `y`'s low bit. Decompression checks the tag and `x < p`, computes `x³ + a x \
  + b` and a square root's candidate by Tonelli and Shanks's descent (`p - 1 = q 2⁹⁶`: 95 rounds \
  of squarings and masked selections, both counters in `r31`), takes it or `p` minus it by the \
  tag's parity, and checks its square and parity. The result (or zeros) is selected by a mask of \
  the checks, without branches, so the time depends only on the pointers."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.EcKey.Compressed.PPC64LE.compressP224
    verified := Proof.EcKey.Compressed.PPC64LE.P224.compress_verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.EcKey.Compressed.PPC64LE.decompressP224
    verified := Proof.EcKey.Compressed.PPC64LE.P224.decompress_verified h.law }]

end VG.Generic.P224.PPC64LE.EcCompressedP224
