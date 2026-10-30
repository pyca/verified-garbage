module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Secp256k1.Lit

/-!
# secp256k1 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/PPC64LE/Law.lean`, which decompression's proof of its square
root uses.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcCompressedSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressSecp256k1
    verified := Proof.EcKey.Compressed.PPC64LE.Secp256k1.compress_verified },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressSecp256k1
    verified := Proof.EcKey.Compressed.PPC64LE.Secp256k1.decompress_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcCompressedSecp256k1
