module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.PPC64LE

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact PPC64LE.target {
    code := Impl.CmacTripleDes.Stream.PPC64LE.Fn.init
    verified := .scrubbed Proof.CmacTripleDes.Stream.PPC64LE.Scrub.init_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact PPC64LE.target {
    code := Impl.CmacTripleDes.Stream.PPC64LE.Fn.absorb
    verified := .scrubbed Proof.CmacTripleDes.Stream.PPC64LE.Scrub.absorb_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact PPC64LE.target {
    code := Impl.CmacTripleDes.Stream.PPC64LE.Fn.finish
    verified := .scrubbed Proof.CmacTripleDes.Stream.PPC64LE.Scrub.finish_scrubbed }]

end VG.Artifacts.CmacTripleDes.PPC64LE
