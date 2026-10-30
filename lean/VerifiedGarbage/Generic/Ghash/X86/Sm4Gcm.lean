module

public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SM4-GCM (NIST SP 800-38D, RFC 8998) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementation `v` of `vg_ghash`, are emitted once for each variant
(`Variants/Ghash/X86/`), named with its suffix (e.g.
`vg_sm4_gcm_seal_pclmul`), and need its CPU features. `vg_sm4_gcm_init`, which
calls no GHASH, is registered once, in `Artifacts/Sm4Gcm/X86.lean`. **Review
note**: each artifact is made from its function's `Api` (in
`Spec/Sm4/Gcm/Contract.lean`, reviewed with the contract).

SM4-GCM's functions share AES-GCM's pieces that only hash or compare
(`Impl/Sm4Gcm/X86.lean`), which take AES-GCM's callees (`GcmImpl`) and
call only their `vg_ghash`: the callees here are `v` with AES-GCM's
baseline `vg_aes_ctr32`, which no SM4-GCM function calls.
`vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`, which only hash and
have AES-GCM's contracts, are AES-GCM's code and proofs
(`Proof/AesGcm/X86/Frame.lean`) under SM4-GCM's names.

The functions that call `vg_sm4_ctr32` use 1536 bytes of stack for the call
(its four arguments, the return address and its own frame); `stream_init`
and `stream_aad`, which call only `vg_ghash` (five arguments), 24. Every
function also keeps its working space of 2560 bytes in a frame of its own,
which copies its arguments passed on the stack: 2584 bytes for
`stream_init`, 2592 for `stream_aad`, 2596 for `stream_finish`, 2600 for
`stream_encrypt`, `stream_decrypt`, `stream_verify` and `seal`, and 2604
for `open`.
-/

@[expose] public section

namespace VG.Generic.Ghash.X86.Sm4Gcm

open VG.Proof.Sm4Gcm.X86
open VG.Proof.AesGcm.X86 (GcmImpl withStackScratch_spSafe)

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit v.callees)
    stack := 2608
    verified := Proof.AesGcm.X86.streamInit_framed v
    spSafe := withStackScratch_spSafe (Proof.AesGcm.X86.streamInit_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamAadApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad v.callees)
    stack := 2616
    verified := Proof.AesGcm.X86.streamAad_framed v
    spSafe := withStackScratch_spSafe (Proof.AesGcm.X86.streamAad_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamEncrypt v.callees)
    stack := 4136
    verified := streamEncrypt_framed v
    spSafe := withStackScratch_spSafe (streamEncrypt_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamDecrypt v.callees)
    stack := 4136
    verified := streamDecrypt_framed v
    spSafe := withStackScratch_spSafe (streamDecrypt_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2596 7 (Impl.Sm4Gcm.X86.streamFinish v.callees)
    stack := 4132
    verified := streamFinish_framed v
    spSafe := withStackScratch_spSafe (streamFinish_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamVerify v.callees)
    stack := 4136
    verified := streamVerify_framed v
    spSafe := withStackScratch_spSafe (streamVerify_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.sealApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.«seal» v.callees)
    stack := 4136
    verified := seal_framed v
    spSafe := withStackScratch_spSafe (seal_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.openApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.Sm4Gcm.X86.«open» v.callees)
    stack := 4140
    verified := open_framed v
    spSafe := withStackScratch_spSafe (open_spSafe v)
    features := v.gh.features }]

/-- The artifacts of a variant, from the implementation of `vg_ghash` it names. -/
def artifacts (v : Proof.AesGcm.X86.GhashName) : List Artifact :=
  artifactsOf ⟨Proof.Aes.X86.Ctr32Impl.scalar, v.impl⟩

end VG.Generic.Ghash.X86.Sm4Gcm
