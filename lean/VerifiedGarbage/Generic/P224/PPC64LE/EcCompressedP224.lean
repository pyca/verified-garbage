module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit

/-! # P-224 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcCompressedP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP224
    verified := Proof.EcKey.Compressed.PPC64LE.P224.compress_verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP224
    verified := Proof.EcKey.Compressed.PPC64LE.P224.decompress_verified h.law }]

end VG.Generic.P224.PPC64LE.EcCompressedP224
