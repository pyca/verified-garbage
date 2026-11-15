module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Verified
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.PPC64LE

open VG.Proof.Sm4Gcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r5
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 Impl.Sm4Gcm.PPC64LE.init)
    verified := init_framed },
  Spec.Sm4.Gcm.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 0
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 Impl.Sm4Gcm.PPC64LE.«seal»)
    verified := seal_framed },
  Spec.Sm4.Gcm.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 Impl.Sm4Gcm.PPC64LE.«open»)
    verified := open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 Impl.AesGcm.PPC64LE.streamInit
    verified := Proof.AesGcm.PPC64LE.streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 Impl.AesGcm.PPC64LE.streamAad
    verified := Proof.AesGcm.PPC64LE.streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamEncrypt)
    verified := streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamDecrypt)
    verified := streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 Impl.Sm4Gcm.PPC64LE.streamFinish)
    verified := streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamVerify)
    verified := streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.PPC64LE
