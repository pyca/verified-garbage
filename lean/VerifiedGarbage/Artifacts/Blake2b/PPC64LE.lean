module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # BLAKE2b (RFC 7693) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blake2b.PPC64LE

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.initB
    verified := .scrubbed Proof.Blake2.PPC64LE.Scrub.initB_scrubbed },
  Spec.Blake2.updateBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.updateB
    verified := .scrubbed Proof.Blake2.PPC64LE.Scrub.updateB_scrubbed },
  Spec.Blake2.finalizeBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.finalizeB
    verified := .scrubbed Proof.Blake2.PPC64LE.Scrub.finalizeB_scrubbed }]

end VG.Artifacts.Blake2b.PPC64LE
