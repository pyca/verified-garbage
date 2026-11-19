module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # P-521 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP521.PPC64LE

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p521Compress,
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p521Decompress,
  Spec.EcKey.P521.publicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p521PublicKey]

end VG.Artifacts.EcP521.PPC64LE
