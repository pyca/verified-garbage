module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Verified
import VerifiedGarbage.Proof.Scrypt.PPC64LE.Scrub
import VerifiedGarbage.Impl.Scrypt.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # scrypt (RFC 7914) on PPC64LE -/

namespace VG.Artifacts.Scrypt.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Scrypt.scryptApi.artifact PPC64LE.target {
    code := Impl.Scrypt.PPC64LE.Fn.scrypt Proof.Scrypt.PPC64LE.Whole.pbkName
      Proof.Scrypt.PPC64LE.Whole.pbkCode
    verified := Proof.Scrypt.PPC64LE.Scrub.scrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Scrypt.PPC64LE
