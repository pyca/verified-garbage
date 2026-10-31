module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CCM (NIST SP 800-38C) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCcm.PPC64LE

open VG.Proof.AesCcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesCcm.PPC64LE.«seal»
    stack := 2688
    verified := seal_framed },
  Spec.Ccm.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesCcm.PPC64LE.«open»
    stack := 2688
    verified := open_framed }]

end VG.Artifacts.AesCcm.PPC64LE
