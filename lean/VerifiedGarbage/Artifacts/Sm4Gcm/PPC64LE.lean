module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.PPC64LE

open VG.Proof.Sm4Gcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ctr32
    stack := 3296
    verified := Proof.Sm4.PPC64LE.Modes.ctr32_framed },
  Spec.Sm4.Gcm.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r5
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 Impl.Sm4Gcm.PPC64LE.init)
    stack := 5888
    verified := init_framed },
  Spec.Sm4.Gcm.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 0
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 Impl.Sm4Gcm.PPC64LE.«seal»)
    stack := 6048
    verified := seal_framed },
  Spec.Sm4.Gcm.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 Impl.Sm4Gcm.PPC64LE.«open»)
    stack := 6064
    verified := open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 Impl.AesGcm.PPC64LE.streamInit
    stack := 2592
    verified := Proof.AesGcm.PPC64LE.streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 Impl.AesGcm.PPC64LE.streamAad
    stack := 2592
    verified := Proof.AesGcm.PPC64LE.streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamEncrypt)
    stack := 5888
    verified := streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamDecrypt)
    stack := 5888
    verified := streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 Impl.Sm4Gcm.PPC64LE.streamFinish)
    stack := 5888
    verified := streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamVerify)
    stack := 5888
    verified := streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.PPC64LE
