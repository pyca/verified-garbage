module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SM4-GCM (NIST SP 800-38D with SM4, RFC 8998) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementation `v` of `vg_ghash`, are emitted once for each
(`Variants/Sm4Gcm/AArch64/`), named with its suffix (e.g.
`vg_sm4_gcm_seal_aes`), and need its CPU features. `vg_sm4_gcm_init`, which
calls no GHASH, is in `Artifacts/Sm4Gcm/AArch64.lean`. **Review note**: `sig`
and `doc` are trusted, as they tie the Rust caller to the contract; these
artifacts are made from each function's `Api` (in `Spec/`, reviewed with the
contract). The emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks against
the contract.

The functions encrypt with `vg_sm4_ctr32` (baseline AArch64, no CPU
features). Their calls (`bl`) keep the return address in `x30`, which they
save in the working space; `vg_sm4_ctr32` uses 3264 bytes of stack below
theirs. `seal` and `open` read their last arguments from the stack. Every
function keeps its working space in a frame of 768 bytes, or, for `seal` and
`open`, 784 bytes that also hold a copy of their stack arguments. `stream_init` and
`stream_aad` are AES-GCM's code and proofs, under SM4-GCM's names.
-/

@[expose] public section

namespace VG.Generic.Sm4Gcm.AArch64.Sm4Gcm

open VG.Proof.Sm4Gcm.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Sm4.Gcm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» v.callees)
    stack := 4048
    verified := seal_framed v
    features := v.features },
  Spec.Sm4.Gcm.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» v.callees)
    stack := 4048
    verified := open_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamEncrypt v.callees)
    stack := 4032
    verified := streamEncrypt_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamDecrypt v.callees)
    stack := 4032
    verified := streamDecrypt_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x5
      (Impl.Sm4Gcm.AArch64.streamFinish v.callees)
    stack := 4032
    verified := streamFinish_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamVerify v.callees)
    stack := 4032
    verified := streamVerify_framed v
    features := v.features }]

/-- `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`: AES-GCM's code and
proofs, calling the implementation of `vg_ghash` the variant `v` names (and no
cipher). -/
def artifactsAes (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x4
      (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    stack := 2560
    verified := Proof.AesGcm.AArch64.streamInit_framed
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)
    features := v.gh.impl.features },
  Spec.Sm4.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x5
      (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    stack := 2560
    verified := Proof.AesGcm.AArch64.streamAad_framed
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)
    features := v.gh.impl.features }]

/-- The artifacts calling the implementation of `vg_ghash` the variant `v` names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf ⟨v.gh.impl⟩ ++ artifactsAes v

end VG.Generic.Sm4Gcm.AArch64.Sm4Gcm
