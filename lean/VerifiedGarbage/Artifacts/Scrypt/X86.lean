module

public import VerifiedGarbage.Proof.Scrypt.X86.BlockMixVerified
public import VerifiedGarbage.Proof.Scrypt.X86.RoMixCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on x86 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86

def artifacts : List Artifact := [
  Spec.Scrypt.salsaApi.artifact X86.target {
    code := Impl.Scrypt.X86.salsa
    verified := Proof.Scrypt.X86.salsa_verified },
  Spec.Scrypt.blockMixApi.artifact X86.target {
    code := Impl.Scrypt.X86.blockMix
    stack := 12
    verified := Proof.Scrypt.X86.BlockMix.blockMix_verified },
  Spec.Scrypt.roMixApi.artifact X86.target {
    code := Impl.Scrypt.X86.roMix
    stack := 36
    verified := Proof.Scrypt.X86.RoMix.roMix_verified }]

end VG.Artifacts.Scrypt.X86
