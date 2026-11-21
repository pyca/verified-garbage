module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.AArch64
public import VerifiedGarbage.Proof.BrainpoolP320r1.AArch64.Law
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP320r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP320r1Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
public import VerifiedGarbage.TCB.AArch64.Print

/-! # brainpoolP320r1 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP320r1.AArch64

open VG.Proof.BrainpoolP320r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyBrainpoolP320r1
    verified := Proof.EcKey.AArch64.BrainpoolP320r1.pk_scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressBrainpoolP320r1
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP320r1.scrubbed hasLaw.inv },
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressBrainpoolP320r1
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP320r1Decompress.scrubbed hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcBrainpoolP320r1.AArch64
