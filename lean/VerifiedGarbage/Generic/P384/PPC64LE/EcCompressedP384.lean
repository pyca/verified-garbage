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

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.compress_verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.decompress_verified h.law }]

end VG.Generic.P384.PPC64LE.EcCompressedP384
