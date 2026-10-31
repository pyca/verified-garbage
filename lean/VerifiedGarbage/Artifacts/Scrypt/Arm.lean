module

public import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Verified
public import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix, scryptROMix and scrypt on 32-bit ARM

`vg_scrypt` calls `vg_pbkdf2_hmac_sha256_scratch` (registered in
`Artifacts/Pbkdf2Sha256/Arm.lean`), the one implementation of PBKDF2-HMAC-SHA256
on this target, and `vg_scrypt_romix`. Its `stack` is the 40 bytes the frame
of PBKDF2's stack arguments and PBKDF2's own frames use.
-/

@[expose] public section

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List Artifact := [
  Spec.Scrypt.salsaApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.salsa
    verified := Proof.Scrypt.Arm.salsa_verified },
  Spec.Scrypt.blockMixApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.blockMix
    verified := Proof.Scrypt.Arm.BlockMix.blockMix_verified },
  Spec.Scrypt.roMixApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.roMix
    verified := Proof.Scrypt.Arm.RoMix.roMix_verified },
  Spec.Scrypt.scryptApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.scrypt Spec.Hmac.sha256I.pbkdf2ScratchApi.name Proof.Scrypt.Arm.Whole.pbkC
    stack := 40
    verified := Proof.Scrypt.Arm.Whole.scrypt_verified }]

end VG.Artifacts.Scrypt.Arm
