module

public import VerifiedGarbage.Impl.EcKey.P224.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.P224.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P224.AArch64.Law
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.TCB.AArch64.Print

/-! # P-224 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP224
    verified := Proof.EcKey.Compressed.AArch64.P224.scrubbed hasLaw.inv },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP224
    verified := Proof.EcKey.Compressed.AArch64.Residue.P224.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P224.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP224
    verified := Proof.EcKey.AArch64.P224.pk_scrubbed hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) }]

end VG.Artifacts.EcP224.AArch64
