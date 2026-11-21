module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CMAC (NIST SP 800-38B) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CmacAes.PPC64LE

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact PPC64LE.target {
    code := Impl.CmacAes.Stream.PPC64LE.Fn.init
    verified := .scrubbed Proof.CmacAes.Stream.PPC64LE.Scrub.init_scrubbed },
  Spec.Cmac.aesAbsorbApi.artifact PPC64LE.target {
    code := Impl.CmacAes.Stream.PPC64LE.Fn.absorb
    verified := .scrubbed Proof.CmacAes.Stream.PPC64LE.Scrub.absorb_scrubbed },
  Spec.Cmac.aesFinishApi.artifact PPC64LE.target {
    code := Impl.CmacAes.Stream.PPC64LE.Fn.finish
    verified := .scrubbed Proof.CmacAes.Stream.PPC64LE.Scrub.finish_scrubbed }]

end VG.Artifacts.CmacAes.PPC64LE
