module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P521.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P521.Lit

/-! # P-521 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcCompressedP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP521
    verified := Proof.EcKey.Compressed.PPC64LE.P521.compress_verified },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP521
    verified := Proof.EcKey.Compressed.PPC64LE.P521.decompress_verified h.law }]

end VG.Generic.P521.PPC64LE.EcCompressedP521
