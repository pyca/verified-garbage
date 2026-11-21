module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Verified
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # scrypt (RFC 7914) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Scrypt.PPC64LE

def artifacts : List Artifact := [
  Spec.Scrypt.scryptApi.artifact PPC64LE.target {
    code := Impl.Scrypt.PPC64LE.Fn.scrypt Proof.Scrypt.PPC64LE.Whole.pbkName
      Proof.Scrypt.PPC64LE.Whole.pbkCode
    verified := Proof.Scrypt.PPC64LE.Scrub.scrypt_scrubbed }]

end VG.Artifacts.Scrypt.PPC64LE
