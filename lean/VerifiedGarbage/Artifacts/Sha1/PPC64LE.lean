module

public import VerifiedGarbage.Proof.Sha1.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SHA-1 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Stream.init
    verified := .scrubbed ⟨Proof.Sha1.PPC64LE.Shared.init, Proof.Sha1.PPC64LE.Stream.init_noResidue _ _⟩ },
  Spec.Sha1.updateApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.update
    verified := .scrubbed Proof.Sha1.PPC64LE.update_scrubbed },
  Spec.Sha1.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Fn.finalize
    verified := .scrubbed Proof.Sha1.PPC64LE.finalize_scrubbed },
  Spec.Sha1.digestApi.artifact PPC64LE.target Proof.Sha1.PPC64LE.digestReg]

end VG.Artifacts.Sha1.PPC64LE
