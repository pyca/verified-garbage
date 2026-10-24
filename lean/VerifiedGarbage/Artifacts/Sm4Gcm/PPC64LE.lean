module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-!
# SM4-GCM (NIST SP 800-38D, RFC 8998) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. Each artifact is made from its function's `Api` (in `Spec/`,
reviewed with the contract), and this file adds only notes on the
implementation.

The AEAD functions are AES-GCM's code (`Impl/AesGcm/PPC64LE.lean`) with SM4's
counter mode and key expansion inlined in place of AES's. They keep
AES-GCM's 2560-byte working space and SM4's 3264-byte one each in a frame of
its own (a frame is less than a page): 2592 and 3296 bytes, or 2672 and 3376
for `seal` and 2672 and 3392 for `open`, whose frames also copy their stack
arguments (`Proof/Sm4Gcm/PPC64LE/Frame.lean`). `stream_init` and
`stream_aad`, which only hash, are AES-GCM's functions themselves, whose
contracts theirs are. `vg_sm4_ctr32` is SM4's counter mode with GCM's
increment, in a frame of 3296 bytes that holds its working space, wiped
before it returns.
-/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.PPC64LE

open VG.Proof.Sm4Gcm.PPC64LE

/-- How SM4 is computed. -/
def sm4Note : String := "Baseline PPC64LE: SM4 bitsliced in general-purpose registers through the AES \
  S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."

/-- How `init` is built. -/
def initNote : String := "Baseline PPC64LE: SM4's key expansion, then its counter mode on the zero \
  block for the hash subkey, inlined, with their working space in a frame of its own."

/-- How `stream_init` and `stream_aad` are built. -/
def ghashNote : String := "AES-GCM's code (`vg_aes_gcm_stream_init`, `vg_aes_gcm_stream_aad`), which \
  reads only the hash subkey of the key context; GHASH with a 4-bit table, with no secret-dependent \
  table lookups."

/-- How the other functions are built. -/
def cryptNote : String := "AES-GCM's code (GHASH with a 4-bit table) with SM4's counter mode inlined \
  in place of AES's, its 3264-byte working space in a frame of its own."

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact PPC64LE.target {
    notes := [sm4Note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ctr32
    stack := 3296
    verified := Proof.Sm4.PPC64LE.Modes.ctr32_framed },
  Spec.Sm4.Gcm.initApi.artifact PPC64LE.target {
    notes := [sm4Note, initNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r5
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 Impl.Sm4Gcm.PPC64LE.init)
    stack := 5888
    verified := init_framed },
  Spec.Sm4.Gcm.sealApi.artifact PPC64LE.target {
    notes := [sm4Note, cryptNote]
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 0
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 Impl.Sm4Gcm.PPC64LE.«seal»)
    stack := 6048
    verified := seal_framed },
  Spec.Sm4.Gcm.openApi.artifact PPC64LE.target {
    notes := [sm4Note, cryptNote]
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 Impl.Sm4Gcm.PPC64LE.«open»)
    stack := 6064
    verified := open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact PPC64LE.target {
    notes := [ghashNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 Impl.AesGcm.PPC64LE.streamInit
    stack := 2592
    verified := Proof.AesGcm.PPC64LE.streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact PPC64LE.target {
    notes := [ghashNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 Impl.AesGcm.PPC64LE.streamAad
    stack := 2592
    verified := Proof.AesGcm.PPC64LE.streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact PPC64LE.target {
    notes := [sm4Note, cryptNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamEncrypt)
    stack := 5888
    verified := streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact PPC64LE.target {
    notes := [sm4Note, cryptNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamDecrypt)
    stack := 5888
    verified := streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact PPC64LE.target {
    notes := [sm4Note, cryptNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 Impl.Sm4Gcm.PPC64LE.streamFinish)
    stack := 5888
    verified := streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact PPC64LE.target {
    notes := [sm4Note, cryptNote]
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamVerify)
    stack := 5888
    verified := streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.PPC64LE
