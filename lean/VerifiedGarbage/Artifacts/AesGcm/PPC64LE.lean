module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # AES-GCM (NIST SP 800-38D) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesGcm.PPC64LE

open VG.Proof.AesGcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Gcm.encryptBlocksApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Blocks.encrypt
    verified := Blocks.encrypt_verified },
  Spec.Gcm.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init
    stack := 2592
    verified := init_framed },
  Spec.Gcm.streamInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 Impl.AesGcm.PPC64LE.streamInit
    stack := 2592
    verified := streamInit_framed },
  Spec.Gcm.streamAadApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 Impl.AesGcm.PPC64LE.streamAad
    stack := 2592
    verified := streamAad_framed },
  Spec.Gcm.streamEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 Impl.AesGcm.PPC64LE.streamEncrypt
    stack := 2592
    verified := streamEncrypt_framed },
  Spec.Gcm.streamDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 Impl.AesGcm.PPC64LE.streamDecrypt
    stack := 2592
    verified := streamDecrypt_framed },
  Spec.Gcm.streamFinishApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9 Impl.AesGcm.PPC64LE.streamFinish
    stack := 2592
    verified := streamFinish_framed },
  Spec.Gcm.streamVerifyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 Impl.AesGcm.PPC64LE.streamVerify
    stack := 2592
    verified := streamVerify_framed },
  Spec.Gcm.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.seal
    stack := 2672
    verified := seal_framed },
  Spec.Gcm.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesGcm.PPC64LE.open
    stack := 2688
    verified := open_framed },
  Spec.Gcm.sealGatherApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.SealGather.sealGather
    stack := 2832
    verified := Gather.sealGather_verified }]

end VG.Artifacts.AesGcm.PPC64LE
