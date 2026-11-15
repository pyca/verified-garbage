module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Init
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-OCB (RFC 7253) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOcb.PPC64LE

open VG.Proof.AesOcb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init
    verified := init_framed },
  Spec.Ocb.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«seal»
    verified := Proof.AesOcb.seal_keyed seal_framed },
  Spec.Ocb.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«open»
    verified := Proof.AesOcb.open_keyed open_framed }]

end VG.Artifacts.AesOcb.PPC64LE
