module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P384.Lit
public import VerifiedGarbage.Proof.P384.PPC64LE.Law

/-! # P-384 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.compress_verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedP384.PPC64LE
