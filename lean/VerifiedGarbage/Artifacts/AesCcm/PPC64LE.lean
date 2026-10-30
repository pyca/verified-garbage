module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CCM (NIST SP 800-38C) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. PPC64LE has one implementation of `vg_cmac_aes_update` and of
`vg_aes_ctr32`, so these are not generic over them.

Both functions run in a frame of 2688 bytes holding their working space
(`Proof/AesCcm/PPC64LE/Verified.lean`). A call (`bl`) stores nothing in
memory, and the functions they call use no stack: their `stack` is that
frame.
-/

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
