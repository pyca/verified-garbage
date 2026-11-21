module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # AES-GCM (NIST SP 800-38D) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesGcm.PPC64LE

open VG.Proof.AesGcm.PPC64LE.Scrub

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.init
    verified := init_scrubbed },
  Spec.Gcm.streamInitApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamInit
    verified := streamInit_scrubbed },
  Spec.Gcm.streamAadApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamAad
    verified := streamAad_scrubbed },
  Spec.Gcm.streamEncryptApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamEncrypt
    verified := streamEncrypt_scrubbed },
  Spec.Gcm.streamDecryptApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamDecrypt
    verified := streamDecrypt_scrubbed },
  Spec.Gcm.streamFinishApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamFinish
    verified := streamFinish_scrubbed },
  Spec.Gcm.streamVerifyApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamVerify
    verified := streamVerify_scrubbed },
  Spec.Gcm.sealApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.seal
    verified := seal_scrubbed },
  Spec.Gcm.openApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.open
    verified := open_scrubbed },
  Spec.Gcm.sealGatherApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.sealGather
    verified := sealGather_scrubbed },
  Spec.Gcm.openToApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.openTo
    verified := openTo_scrubbed }]

end VG.Artifacts.AesGcm.PPC64LE
