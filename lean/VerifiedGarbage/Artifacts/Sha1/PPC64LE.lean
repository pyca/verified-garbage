module

public import VerifiedGarbage.Proof.Sha1.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SHA-1 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Stream.init
    verified := Proof.Sha1.PPC64LE.init_scrubbed },
  Spec.Sha1.updateApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.update
    verified := Proof.Sha1.PPC64LE.update_scrubbed },
  Spec.Sha1.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.finalize
    verified := Proof.Sha1.PPC64LE.finalize_scrubbed },
  Spec.Sha1.digestApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.digest
    verified := Proof.Sha1.PPC64LE.digest_scrubbed }]

end VG.Artifacts.Sha1.PPC64LE
