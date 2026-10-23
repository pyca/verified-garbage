module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix, scryptROMix and scrypt on PPC64LE
-/

@[expose] public section

namespace VG.Artifacts.Scrypt.PPC64LE

def artifacts : List Artifact := [
  Spec.Scrypt.salsaApi.artifact PPC64LE.target {
    code := Impl.Scrypt.PPC64LE.salsa
    verified := Proof.Scrypt.PPC64LE.salsa_verified },
  Spec.Scrypt.blockMixApi.artifact PPC64LE.target {
    code := Impl.Scrypt.PPC64LE.blockMix
    stack := 48
    verified := Proof.Scrypt.PPC64LE.BlockMix.blockMix_verified },
  Spec.Scrypt.roMixApi.artifact PPC64LE.target {
    notes := ["The function has no stack frame of its own: its return address is saved in `scratch`."]
    code := Impl.Scrypt.PPC64LE.roMix
    stack := 48
    verified := Proof.Scrypt.PPC64LE.RoMix.roMix_verified },
  Spec.Scrypt.scryptApi.artifact PPC64LE.target {
    notes := ["Derives both keys with `vg_pbkdf2_hmac_sha256_scratch` and runs scryptROMix on each \
      block with `vg_scrypt_romix`, using the start of `scratch` as the working space of each. The \
      return address, the caller's `r30` and the arguments the calls do not keep are saved in a \
      112-byte stack frame, to which `r30` points; the calls use the 1008 bytes below it."]
    code := Impl.Scrypt.PPC64LE.Whole.scrypt Proof.Scrypt.PPC64LE.Whole.pbkName
      Proof.Scrypt.PPC64LE.Whole.pbkCode
    stack := 1120
    verified := Proof.Scrypt.PPC64LE.Whole.scrypt_verified }]

end VG.Artifacts.Scrypt.PPC64LE
