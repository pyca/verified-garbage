module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-SIV (RFC 5297) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact PPC64LE.target {
    code := Impl.AesSiv.PPC64LE.Fn.init
    verified := Proof.AesSiv.PPC64LE.Scrub.init_scrubbed },
  Spec.Siv.encryptApi.artifact PPC64LE.target {
    code := Impl.AesSiv.PPC64LE.Fn.encrypt
    verified := Proof.AesSiv.PPC64LE.Scrub.encrypt_scrubbed },
  Spec.Siv.decryptApi.artifact PPC64LE.target {
    code := Impl.AesSiv.PPC64LE.Fn.decrypt
    verified := Proof.AesSiv.PPC64LE.Scrub.decrypt_scrubbed }]

end VG.Artifacts.AesSiv.PPC64LE
