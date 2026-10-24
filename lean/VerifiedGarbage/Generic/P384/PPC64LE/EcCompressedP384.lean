module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P384.Lit

/-!
# P-384 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/PPC64LE/Law.lean`, which decompression's proof of its square
root uses.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcCompressedP384

/-- How the functions work. -/
def notes : List String := ["The functions are `vg_ecdh_p384`'s setup, field arithmetic and checks: they save `r14`, `r31` \
  and `lr` in `scratch` (in `r3` during the function), keep `out` in `r14` and `public` in `r12` \
  while they read it; field elements are six 64-bit words in Montgomery form, multiplied by calls \
  of `vg_p384_mul_mod_p` and the other functions of `p384_mont`. Compression checks the key as \
  ECDH checks the peer's (its first byte, both coordinates below `p` and the curve's equation) and \
  writes the tag from `y`'s low bit. Decompression checks the tag and `x < p`, computes `x³ + a x \
  + b` and a square root's candidate by `rhs^((p+1)/4)`, by square-and-always-multiply, takes it \
  or `p` minus it by the tag's parity, and checks its square and parity. The result (or zeros) is \
  selected by a mask of the checks, without branches, so the time depends only on the pointers."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.EcKey.Compressed.PPC64LE.compressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.compress_verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.EcKey.Compressed.PPC64LE.decompressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.decompress_verified h.law }]

end VG.Generic.P384.PPC64LE.EcCompressedP384
