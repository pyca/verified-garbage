module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on PPC64LE
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
    verified := Proof.Scrypt.PPC64LE.RoMix.roMix_verified }]

end VG.Artifacts.Scrypt.PPC64LE
