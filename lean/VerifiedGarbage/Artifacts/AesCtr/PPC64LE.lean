module

public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CTR (NIST SP 800-38A §6.5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCtr.PPC64LE

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ctr
    verified := .scrubbed Proof.Aes.PPC64LE.Scrub.ctr_scrubbed },
  Spec.Ctr.aesFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ctrFinal
    verified := .scrubbed Proof.Aes.PPC64LE.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.AesCtr.PPC64LE
