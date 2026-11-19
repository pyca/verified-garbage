module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P224.PPC64LE.Law

/-! # P-224 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p224Compress,
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact PPC64LE.target (Proof.EcKey.PPC64LE.Scrub.p224Decompress hasLaw.law),
  Spec.EcKey.P224.publicKeyApi.artifact PPC64LE.target (Proof.EcKey.PPC64LE.Scrub.p224PublicKey hasLaw.law)]

end VG.Artifacts.EcP224.PPC64LE
