module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CCM (NIST SP 800-38C) on PPC64LE -/

namespace VG.Artifacts.AesCcm.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ccm.sealApi.artifact PPC64LE.target {
    code := Impl.AesCcm.PPC64LE.Fn.seal
    verified := Proof.AesCcm.PPC64LE.Scrub.seal_scrubbed },
  Spec.Ccm.openApi.artifact PPC64LE.target {
    code := Impl.AesCcm.PPC64LE.Fn.open
    verified := Proof.AesCcm.PPC64LE.Scrub.open_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCcm.PPC64LE
