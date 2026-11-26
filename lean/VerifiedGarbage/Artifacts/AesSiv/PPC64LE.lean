module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-SIV (RFC 5297) on PPC64LE -/

namespace VG.Artifacts.AesSiv.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Siv.initApi.artifact PPC64LE.target {
    code := Impl.AesSiv.PPC64LE.Fn.init
    verified := Proof.AesSiv.PPC64LE.Scrub.init_scrubbed },
  Spec.Siv.encryptApi.artifact PPC64LE.target {
    code := Impl.AesSiv.PPC64LE.Fn.encrypt
    verified := Proof.AesSiv.PPC64LE.Scrub.encrypt_scrubbed },
  Spec.Siv.decryptApi.artifact PPC64LE.target {
    code := Impl.AesSiv.PPC64LE.Fn.decrypt
    verified := Proof.AesSiv.PPC64LE.Scrub.decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesSiv.PPC64LE
