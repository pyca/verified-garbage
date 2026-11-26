module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Final
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CTR (NIST SP 800-38A §6.5) on PPC64LE -/

namespace VG.Artifacts.AesCtr.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ctr.aesApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ctr
    verified := Proof.Aes.PPC64LE.Scrub.ctr_scrubbed },
  Spec.Ctr.aesFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ctrFinal
    verified := Proof.Aes.PPC64LE.Scrub.ctrFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCtr.PPC64LE
