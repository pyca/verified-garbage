module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OCB (RFC 7253) on PPC64LE -/

namespace VG.Artifacts.AesOcb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ocb.initApi.artifact PPC64LE.target {
    code := Impl.AesOcb.PPC64LE.Fn.init
    verified := Proof.AesOcb.PPC64LE.Scrub.init_scrubbed },
  Spec.Ocb.sealApi.artifact PPC64LE.target {
    code := Impl.AesOcb.PPC64LE.Fn.seal
    verified := Proof.AesOcb.PPC64LE.Scrub.seal_scrubbed },
  Spec.Ocb.openApi.artifact PPC64LE.target {
    code := Impl.AesOcb.PPC64LE.Fn.open
    verified := Proof.AesOcb.PPC64LE.Scrub.open_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesOcb.PPC64LE
