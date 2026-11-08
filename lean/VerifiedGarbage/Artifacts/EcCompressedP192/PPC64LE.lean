module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P192.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P192.Lit
public import VerifiedGarbage.Proof.P192.PPC64LE.Law

/-! # P-192 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP192.PPC64LE

open VG.Proof.P192.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP192
    verified := Proof.EcKey.Compressed.PPC64LE.P192.compress_verified },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP192
    verified := Proof.EcKey.Compressed.PPC64LE.P192.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedP192.PPC64LE
