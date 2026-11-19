module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP512r1.PPC64LE

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp512r1PublicKey,
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp512r1Compress,
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp512r1Decompress]

end VG.Artifacts.EcBrainpoolP512r1.PPC64LE
