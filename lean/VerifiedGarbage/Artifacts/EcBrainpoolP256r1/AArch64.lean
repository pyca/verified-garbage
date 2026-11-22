module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Proof.BrainpoolP256r1.AArch64.Law
public import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.TCB.AArch64.Print

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.AArch64

open VG.Proof.BrainpoolP256r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyBrainpoolP256r1
    verified := Proof.EcKey.AArch64.BrainpoolP256r1.pk_scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressBrainpoolP256r1
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1.scrubbed hasLaw.inv },
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressBrainpoolP256r1
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP256r1Decompress.scrubbed hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcBrainpoolP256r1.AArch64
