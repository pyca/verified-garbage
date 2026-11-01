module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914): Salsa20/8, scryptBlockMix, scryptROMix and scrypt on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Scrypt.PPC64LE

def artifacts : List Artifact := [
  Spec.Scrypt.scryptApi.artifact PPC64LE.target {
    code := Impl.Scrypt.PPC64LE.Whole.scrypt Proof.Scrypt.PPC64LE.Whole.pbkName
      Proof.Scrypt.PPC64LE.Whole.pbkCode
    stack := 1120
    verified := Proof.Scrypt.PPC64LE.Whole.scrypt_verified }]

end VG.Artifacts.Scrypt.PPC64LE
