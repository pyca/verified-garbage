module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.PPC64LE.Law

/-! # brainpoolP320r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP320r1.PPC64LE

open VG.Proof.BrainpoolP320r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact PPC64LE.target (Proof.EcKey.PPC64LE.Scrub.brainpoolp320r1PublicKey hasLaw.law),
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp320r1Compress,
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact PPC64LE.target (Proof.EcKey.PPC64LE.Scrub.brainpoolp320r1Decompress hasLaw.law)]

end VG.Artifacts.EcBrainpoolP320r1.PPC64LE
