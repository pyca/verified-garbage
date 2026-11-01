module

public import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Verified
public import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914): Salsa20/8, scryptBlockMix, scryptROMix and scrypt on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List Artifact := [
  Spec.Scrypt.scryptApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.scrypt "vg_pbkdf2_hmac_sha256_scratch" Proof.Scrypt.Arm.Whole.pbkC
    stack := 40
    verified := Proof.Scrypt.Arm.Whole.scrypt_verified }]

end VG.Artifacts.Scrypt.Arm
