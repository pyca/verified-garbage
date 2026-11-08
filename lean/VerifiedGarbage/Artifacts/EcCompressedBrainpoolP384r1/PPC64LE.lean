module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.BrainpoolP384r1.PPC64LE.Law

/-! # brainpoolP384r1 point compression and decompression (SEC 1 §§2.3.3–2.3.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP384r1.PPC64LE

open VG.Proof.BrainpoolP384r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.compress_verified },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.decompress_verified hasLaw.law }]

end VG.Artifacts.EcCompressedBrainpoolP384r1.PPC64LE
