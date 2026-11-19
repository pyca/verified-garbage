module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP384r1.PPC64LE

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp384r1PublicKey,
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp384r1Compress,
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.brainpoolp384r1Decompress]

end VG.Artifacts.EcBrainpoolP384r1.PPC64LE
