module

public import VerifiedGarbage.Impl.EcKey.P256.AArch64
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Residue
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P256.AArch64.Law
public import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.TCB.AArch64.Print

/-! # P-256 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP256
    verified := Proof.EcKey.Compressed.AArch64.P256.scrubbed hasLaw.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP256
    verified := Proof.EcKey.Compressed.AArch64.Residue.P256.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P256.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP256
    verified := Proof.EcKey.AArch64.booth_pk_scrubbed hasLaw.law hasLaw.inv (Proof.P256.combOk7 hasLaw.law) }]

end VG.Artifacts.EcP256.AArch64
