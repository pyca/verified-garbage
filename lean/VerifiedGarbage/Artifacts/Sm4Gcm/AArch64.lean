module

public import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Variants.Sm4Gcm.AArch64

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on AArch64 -/

@[expose] public section

-- SM4-GCM (NIST SP 800-38D with SM4, RFC 8998) on AArch64
namespace VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

open VG.Proof.Sm4Gcm.AArch64

/-- The artifacts calling the implementations the variant `v` names, in
their frames, zeroed whole on return. -/
def artifactsOf (v : GcmVariant) (hv : v ∈ VG.Proof.Variants.Sm4Gcm.AArch64.variants) : List Artifact := [
  Spec.Sm4.Gcm.sealApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := seal_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.sealOk _ (Nat.zero_lt_succ _))
    (Proof.Sm4Gcm.AArch64.Scrub.sealSide v hv)),
  Spec.Sm4.Gcm.openApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := open_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.openOk _)
    (Proof.Sm4Gcm.AArch64.Scrub.openSide v hv)),
  Spec.Sm4.Gcm.streamEncryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamEncrypt (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := streamEncrypt_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.streamEncryptOk _ (Proof.Sm4Gcm.AArch64.Scrub.pos768 _))
    (Proof.Sm4Gcm.AArch64.Scrub.streamEncryptSide v hv)),
  Spec.Sm4.Gcm.streamDecryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamDecrypt (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := streamDecrypt_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.streamDecryptOk _ (Proof.Sm4Gcm.AArch64.Scrub.pos768 _))
    (Proof.Sm4Gcm.AArch64.Scrub.streamDecryptSide v hv)),
  Spec.Sm4.Gcm.streamFinishApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x5
      (Impl.Sm4Gcm.AArch64.streamFinish (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := streamFinish_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.streamFinishOk _ (Proof.Sm4Gcm.AArch64.Scrub.pos768 _))
    (Proof.Sm4Gcm.AArch64.Scrub.streamFinishSide v hv)),
  Spec.Sm4.Gcm.streamVerifyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamVerify (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := streamVerify_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.streamVerifyOk _ (Proof.Sm4Gcm.AArch64.Scrub.pos768 _))
    (Proof.Sm4Gcm.AArch64.Scrub.streamVerifySide v hv))]

/-- `vg_sm4_gcm_init`, which calls only the implementation of `vg_sm4_ctr32`. -/
def artifactsInit (v : GcmVariant) (hv : v ∈ VG.Proof.Variants.Sm4Gcm.AArch64.variants) : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).ctrSuffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x2 (Impl.Sm4Gcm.AArch64.init (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := init_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.Sm4Gcm.AArch64.Scrub.initOk _ (Proof.Sm4Gcm.AArch64.Scrub.pos768 _))
    (Proof.Sm4Gcm.AArch64.Scrub.initSide v hv))]

/-- `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`: AES-GCM's code and
proofs, calling the implementation of `vg_ghash` the variant `v` names (and no
cipher). -/
def artifactsAes (v : GcmVariant) (hv : v ∈ VG.Proof.Variants.Sm4Gcm.AArch64.variants) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x4
      (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    verified := Proof.AesGcm.AArch64.streamInit_framedW
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamInitOk _ (Proof.AesGcm.AArch64.gcmWn_pos _))
    (Proof.Sm4Gcm.AArch64.Scrub.streamInitSide v hv)),
  Spec.Sm4.Gcm.streamAadApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x5
      (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    verified := Proof.AesGcm.AArch64.streamAad_framedW
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamAadOk _ (Proof.AesGcm.AArch64.gcmWn_pos _))
    (Proof.Sm4Gcm.AArch64.Scrub.streamAadSide v hv))]

/-- The artifacts calling the implementations the variant `v` names: those
that call only one of the two with the baseline implementation of the other,
of which the other variants would be the same functions. -/
def artifacts (v : GcmVariant) (hv : v ∈ VG.Proof.Variants.Sm4Gcm.AArch64.variants) : List Artifact :=
  (match v.gh with
    | .scalar => artifactsInit v hv
    | .aes | .neon => []) ++
  artifactsOf v hv ++
  (match v.ctr with
    | .scalar => artifactsAes v hv
    | .sm4 => [])

end VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

namespace VG.Artifacts.Sm4Gcm.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.Sm4Gcm.AArch64.variants.attach.flatMap fun ⟨v, hv⟩ => Sm4Gcm.artifacts v hv

end VG.Artifacts.Sm4Gcm.AArch64
