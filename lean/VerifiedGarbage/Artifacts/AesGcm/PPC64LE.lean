module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM (NIST SP 800-38D) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. Each function keeps its working space in a frame of its own, of
2592 bytes, or 2672 for `seal` and 2688 for `open`, whose frames also copy
their stack arguments (`Proof/AesGcm/PPC64LE/Frame.lean`); the functions it
calls use no stack. `seal_gather` copies the slices to `dst` and calls
`seal` on them, from a frame of 160 bytes below which `seal` keeps its own
(`Proof/AesGcm/PPC64LE/Gather/`).
-/

@[expose] public section

namespace VG.Artifacts.AesGcm.PPC64LE

open VG.Proof.AesGcm.PPC64LE

/-- How `init` is built. -/
def initNote : String := "This implementation calls `vg_aes_expand_key_scratch` for the key schedule and \
  `vg_aes_ctr32` to encrypt the zero block into the hash subkey."

/-- How `stream_init` and `stream_aad` are built. -/
def ghashNote : String := "This implementation calls `vg_ghash` for GHASH."

/-- How `seal_gather` is built. -/
def gatherNote : String :=
  "This implementation copies the slices `src` lists to `dst`, one after the other, and then \
    encrypts them there in place with `" ++ Spec.Gcm.sealApi.name ++ "`."

/-- How the other functions are built. -/
def callNote : String := "This implementation calls `vg_aes_ctr32` for the block cipher and `vg_ghash` for GHASH."

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact PPC64LE.target {
    notes := [initNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init
    stack := 2592
    verified := init_framed },
  Spec.Gcm.streamInitApi.artifact PPC64LE.target {
    notes := [ghashNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 Impl.AesGcm.PPC64LE.streamInit
    stack := 2592
    verified := streamInit_framed },
  Spec.Gcm.streamAadApi.artifact PPC64LE.target {
    notes := [ghashNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 Impl.AesGcm.PPC64LE.streamAad
    stack := 2592
    verified := streamAad_framed },
  Spec.Gcm.streamEncryptApi.artifact PPC64LE.target {
    notes := [callNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 Impl.AesGcm.PPC64LE.streamEncrypt
    stack := 2592
    verified := streamEncrypt_framed },
  Spec.Gcm.streamDecryptApi.artifact PPC64LE.target {
    notes := [callNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 Impl.AesGcm.PPC64LE.streamDecrypt
    stack := 2592
    verified := streamDecrypt_framed },
  Spec.Gcm.streamFinishApi.artifact PPC64LE.target {
    notes := [callNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9 Impl.AesGcm.PPC64LE.streamFinish
    stack := 2592
    verified := streamFinish_framed },
  Spec.Gcm.streamVerifyApi.artifact PPC64LE.target {
    notes := [callNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 Impl.AesGcm.PPC64LE.streamVerify
    stack := 2592
    verified := streamVerify_framed },
  Spec.Gcm.sealApi.artifact PPC64LE.target {
    notes := [callNote]
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.seal
    stack := 2672
    verified := seal_framed },
  Spec.Gcm.openApi.artifact PPC64LE.target {
    notes := [callNote]
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesGcm.PPC64LE.open
    stack := 2688
    verified := open_framed },
  Spec.Gcm.sealGatherApi.artifact PPC64LE.target {
    notes := [gatherNote]
    code := Impl.AesGcm.PPC64LE.SealGather.sealGather
    stack := 2832
    verified := Gather.sealGather_verified }]

end VG.Artifacts.AesGcm.PPC64LE
