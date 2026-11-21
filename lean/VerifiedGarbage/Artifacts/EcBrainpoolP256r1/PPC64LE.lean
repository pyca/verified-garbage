module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.PPC64LE.Law

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.PPC64LE

open VG.Proof.BrainpoolP256r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp256r1PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.brainpoolp256r1PublicKey_scrubbed hasLaw.law },
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp256r1Compress
    verified := Proof.EcKey.PPC64LE.Scrub.brainpoolp256r1Compress_scrubbed },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp256r1Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.brainpoolp256r1Decompress_scrubbed hasLaw.law }]

end VG.Artifacts.EcBrainpoolP256r1.PPC64LE
