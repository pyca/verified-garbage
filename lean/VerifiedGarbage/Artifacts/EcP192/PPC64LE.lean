module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # P-192 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP192.PPC64LE

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p192Compress,
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p192Decompress,
  Spec.EcKey.P192.publicKeyApi.artifact PPC64LE.target Proof.EcKey.PPC64LE.Scrub.p192PublicKey]

end VG.Artifacts.EcP192.PPC64LE
