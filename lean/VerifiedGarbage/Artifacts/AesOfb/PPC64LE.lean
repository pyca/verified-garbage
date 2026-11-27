module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
import VerifiedGarbage.Proof.AesOfb.PPC64LE.Final
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OFB (NIST SP 800-38A §6.4) on PPC64LE -/

namespace VG.Artifacts.AesOfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ofb.aesApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ofb
    verified := Proof.Aes.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Ofb.aesFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ofbFinal
    verified := Proof.Aes.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesOfb.PPC64LE
