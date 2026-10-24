module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.Lit

/-!
# brainpoolP512r1 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/PPC64LE/Law.lean`, which decompression's proof of its square
root uses.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.PPC64LE.EcCompressedBrainpoolP512r1

/-- How the functions work. -/
def notes : List String := ["The functions are `vg_ecdh_brainpoolp512r1`'s setup, field arithmetic and checks: they save \
  `r14`, `r31` and `lr` in `scratch` (in `r3` during the function), keep `out` in `r14` and \
  `public` in `r12` while they read it; field elements are eight 64-bit words in Montgomery form, \
  multiplied by calls of `vg_brainpoolp512r1_mul_mod_p` and the other functions of \
  `brainpoolp512r1_mont`. Compression checks the key as ECDH checks the peer's (its first byte, \
  both coordinates below `p` and the curve's equation) and writes the tag from `y`'s low bit. \
  Decompression checks the tag and `x < p`, computes `x³ + a x + b` and a square root's candidate \
  by `rhs^((p+1)/4)`, by square-and-always-multiply, takes it or `p` minus it by the tag's parity, \
  and checks its square and parity. The result (or zeros) is selected by a mask of the checks, \
  without branches, so the time depends only on the pointers."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.compress_verified },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.decompress_verified h.law }]

end VG.Generic.BrainpoolP512r1.PPC64LE.EcCompressedBrainpoolP512r1
