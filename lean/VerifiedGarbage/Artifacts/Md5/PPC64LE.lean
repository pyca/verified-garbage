module

public import VerifiedGarbage.Proof.Md5.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # MD5 (RFC 1321) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Md5.PPC64LE

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Stream.init
    verified := .scrubbed Proof.Md5.PPC64LE.init_scrubbed },
  Spec.Md5.updateApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Fn.update
    verified := .scrubbed Proof.Md5.PPC64LE.update_scrubbed },
  Spec.Md5.finalizeApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Fn.finalize
    verified := .scrubbed Proof.Md5.PPC64LE.finalize_scrubbed }]

end VG.Artifacts.Md5.PPC64LE
