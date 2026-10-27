module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Resident.Verified
public import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on AArch64
-/

@[expose] public section

namespace VG.Artifacts.Scrypt.AArch64

def artifacts : List Artifact := [
  Spec.Scrypt.salsaApi.artifact AArch64.target {
    code := Impl.Scrypt.AArch64.salsa
    verified := Proof.Scrypt.AArch64.salsa_verified },
  Spec.Scrypt.blockMixApi.artifact AArch64.target {
    code := Impl.Scrypt.AArch64.blockMix
    stack := 16
    verified := Proof.Scrypt.AArch64.Resident.blockMix_verified },
  Spec.Scrypt.roMixApi.artifact AArch64.target {
    code := Impl.Scrypt.AArch64.roMix
    stack := 16
    verified := Proof.Scrypt.AArch64.RoMix.roMix_verified }]

end VG.Artifacts.Scrypt.AArch64
