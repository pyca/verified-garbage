module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P384.PPC64LE.Law

/-! # P-384 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p384Compress,
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target (Proof.EcKey.PPC64LE.Scrub.p384Decompress hasLaw.law),
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target (Proof.EcKey.PPC64LE.Scrub.p384PublicKey hasLaw.law)]

end VG.Artifacts.EcP384.PPC64LE
