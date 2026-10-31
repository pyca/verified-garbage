module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Init
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-OCB (RFC 7253) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOcb.PPC64LE

open VG.Proof.AesOcb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init
    stack := 2592
    verified := init_framed },
  Spec.Ocb.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«seal»
    stack := 2688
    verified := seal_framed },
  Spec.Ocb.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«open»
    stack := 2688
    verified := open_framed }]

end VG.Artifacts.AesOcb.PPC64LE
