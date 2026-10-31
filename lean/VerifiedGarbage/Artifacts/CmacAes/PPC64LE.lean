module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Verified
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CMAC (NIST SP 800-38B) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. PPC64LE has one implementation of the block functions, so these are
not generic over them. A call (`bl`) stores nothing in memory, so
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize` use
no stack.

The streaming functions keep their working space in a frame of their own
on the stack (`Proof/CmacAes/Stream/PPC64LE/Frame.lean`): their `stack` is
that frame.
-/

@[expose] public section

namespace VG.Artifacts.CmacAes.PPC64LE

open VG.Proof.CmacAes.PPC64LE

def artifacts : List Artifact := [
  Spec.Cmac.aesSubkeysApi.artifact PPC64LE.target {
    code := Impl.CmacAes.PPC64LE.subkeys
    verified := subkeys_verified },
  Spec.Cmac.aesUpdateApi.artifact PPC64LE.target {
    code := Impl.CmacAes.PPC64LE.update
    verified := update_verified },
  Spec.Cmac.aesFinalizeApi.artifact PPC64LE.target {
    code := Impl.CmacAes.PPC64LE.finalize
    verified := finalize_verified },
  Spec.Cmac.aesInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r6 Impl.CmacAes.Stream.PPC64LE.init
    stack := 2336
    verified := Proof.CmacAes.Stream.PPC64LE.init_framed },
  Spec.Cmac.aesAbsorbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r8 Impl.CmacAes.Stream.PPC64LE.absorb
    stack := 2336
    verified := Proof.CmacAes.Stream.PPC64LE.absorb_framed },
  Spec.Cmac.aesFinishApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r7 Impl.CmacAes.Stream.PPC64LE.finish
    stack := 2336
    verified := Proof.CmacAes.Stream.PPC64LE.finish_framed }]

end VG.Artifacts.CmacAes.PPC64LE
