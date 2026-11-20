module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CCM (NIST SP 800-38C) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact PPC64LE.target {
    code := Impl.AesCcm.PPC64LE.Fn.seal
    verified := .scrubbed Proof.AesCcm.PPC64LE.Scrub.seal_scrubbed },
  Spec.Ccm.openApi.artifact PPC64LE.target {
    code := Impl.AesCcm.PPC64LE.Fn.open
    verified := .scrubbed Proof.AesCcm.PPC64LE.Scrub.open_scrubbed }]

end VG.Artifacts.AesCcm.PPC64LE
