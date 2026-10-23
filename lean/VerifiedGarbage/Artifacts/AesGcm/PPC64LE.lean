module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM (NIST SP 800-38D) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. Each function keeps its working space in a frame of its own, of
2592 bytes (`Proof/AesGcm/PPC64LE/Frame.lean`); the functions it calls use
no stack.
-/

@[expose] public section

namespace VG.Artifacts.AesGcm.PPC64LE

open VG.Proof.AesGcm.PPC64LE

/-- How `init` is built. -/
def initNote : String := "This implementation calls `vg_aes_expand_key_scratch` for the key schedule and \
  `vg_aes_ctr32` to encrypt the zero block into the hash subkey."

/-- How `stream_init` and `stream_aad` are built. -/
def ghashNote : String := "This implementation calls `vg_ghash` for GHASH."

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
    verified := streamDecrypt_framed }]

end VG.Artifacts.AesGcm.PPC64LE
