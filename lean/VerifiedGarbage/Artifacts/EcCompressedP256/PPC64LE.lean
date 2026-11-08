module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Lit
public import VerifiedGarbage.Proof.P256.PPC64LE.Law

/-! # P-256 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP256
    verified := Proof.EcKey.Compressed.PPC64LE.P256.compress_verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP256
    verified := Proof.EcKey.Compressed.PPC64LE.P256.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedP256.PPC64LE
