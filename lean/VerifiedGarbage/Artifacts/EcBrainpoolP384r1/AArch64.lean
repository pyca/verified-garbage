module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Impl.EcKey.BrainpoolP384r1.AArch64
import VerifiedGarbage.Proof.BrainpoolP384r1.AArch64.Law
import VerifiedGarbage.Proof.EcKey.AArch64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcBrainpoolP384r1.AArch64

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyBrainpoolP384r1
    verified := Proof.EcKey.AArch64.BrainpoolP384r1.pk_scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1.scrubbed hasLaw.inv },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.AArch64.BrainpoolP384r1Decompress.scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcBrainpoolP384r1.AArch64
