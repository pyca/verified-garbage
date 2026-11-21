module

public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ofb
    verified := Proof.Aes.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Ofb.aesFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ofbFinal
    verified := Proof.Aes.PPC64LE.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.AesOfb.PPC64LE
