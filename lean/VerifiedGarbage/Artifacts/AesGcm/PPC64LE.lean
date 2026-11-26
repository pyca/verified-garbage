module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Contiguous
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Scrub
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Verified
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks.Lit
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # AES-GCM (NIST SP 800-38D) on PPC64LE -/

namespace VG.Artifacts.AesGcm.PPC64LE

open VG.Proof.AesGcm.PPC64LE.Scrub

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Gcm.initApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.init
    verified := Proof.AesGcm.PPC64LE.Scrub.init_scrubbed },
  Spec.Gcm.streamInitApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamInit
    verified := Proof.AesGcm.PPC64LE.Scrub.streamInit_scrubbed },
  Spec.Gcm.streamAadApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamAad
    verified := Proof.AesGcm.PPC64LE.Scrub.streamAad_scrubbed },
  Spec.Gcm.streamEncryptApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamEncrypt
    verified := Proof.AesGcm.PPC64LE.Scrub.streamEncrypt_scrubbed },
  Spec.Gcm.streamDecryptApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamDecrypt
    verified := Proof.AesGcm.PPC64LE.Scrub.streamDecrypt_scrubbed },
  Spec.Gcm.streamFinishApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamFinish
    verified := Proof.AesGcm.PPC64LE.Scrub.streamFinish_scrubbed },
  Spec.Gcm.streamVerifyApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.streamVerify
    verified := Proof.AesGcm.PPC64LE.Scrub.streamVerify_scrubbed },
  Spec.Gcm.sealApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.seal
    verified := Proof.AesGcm.PPC64LE.Scrub.seal_scrubbed },
  Spec.Gcm.openApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.open
    verified := Proof.AesGcm.PPC64LE.Scrub.open_scrubbed },
  Spec.Gcm.sealContiguousApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Contiguous.code
    verified := Proof.AesGcm.PPC64LE.Contiguous.scrubbed },
  Spec.Gcm.sealGatherApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.sealGather
    verified := Proof.AesGcm.PPC64LE.Scrub.sealGather_scrubbed },
  Spec.Gcm.openToApi.artifact PPC64LE.target {
    code := Impl.AesGcm.PPC64LE.Fn.openTo
    verified := Proof.AesGcm.PPC64LE.Scrub.openTo_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesGcm.PPC64LE
