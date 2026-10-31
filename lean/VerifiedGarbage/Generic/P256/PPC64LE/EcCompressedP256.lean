module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Lit

/-!
# P-256 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/PPC64LE/Law.lean`, which decompression's proof of its square
root uses.
-/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcCompressedP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP256
    verified := Proof.EcKey.Compressed.PPC64LE.P256.compress_verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP256
    verified := Proof.EcKey.Compressed.PPC64LE.P256.decompress_verified h.law }]

end VG.Generic.P256.PPC64LE.EcCompressedP256
