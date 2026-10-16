module

public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM (NIST SP 800-38D) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32` with its `vg_aes_expand_key_scratch` and of
`vg_ghash`, are emitted once for each combination (`Variants/AesGcm/X86/`),
named with its suffix (e.g. `vg_aes_gcm_seal_aesni_pclmul`), and need its CPU
features: `init` only AES's, `stream_init` and `stream_aad` only GHASH's.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller
to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function calls `vg_aes_ctr32` (six stack arguments) or `vg_ghash`
(five) in a frame of its own, so uses 28 bytes of stack with the return
address (24 for `stream_init` and `stream_aad`, which call only
`vg_ghash`). Every function also keeps its working space in a frame of its own, which
copies its arguments passed on the stack: 2580 bytes for `init`, 2584 for
`stream_init`, 2592 for `stream_aad`, 2600 for `stream_finish`, 2604 for
`stream_encrypt`, `stream_decrypt`, `stream_verify` and `seal`, and 2608 for
`open`. `seal_gather` copies the slices to `dst` and calls `seal` on them
there, from a frame of 48 bytes (`Proof/AesGcm/X86/Gather/`).
-/

@[expose] public section

namespace VG.Generic.AesGcm.X86.AesGcm

open VG.Proof.AesGcm.X86

/-- How the functions are built, and which implementations they call. -/
def callNote (v : GcmImpl) : String :=
  "This implementation calls `" ++ v.ctr.callee.name ++ "`, `" ++ v.gh.fn.name ++ "` and `" ++
    v.ctr.expand.name ++ "` for the block cipher, GHASH and the key schedule, with the arguments it \
    keeps in the working space."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesGcm.X86.init v.callees)
    stack := 2608
    verified := init_framed v
    spSafe := withStackScratch_spSafe (by decide) (init_spSafe v)
    features := (v.ctr.features) },
  Spec.Gcm.streamAadApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad v.callees)
    stack := 2616
    verified := streamAad_framed v
    spSafe := withStackScratch_spSafe (by decide) (streamAad_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamInitApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit v.callees)
    stack := 2608
    verified := streamInit_framed v
    spSafe := withStackScratch_spSafe (by decide) (streamInit_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamEncrypt v.callees)
    stack := 2632
    verified := streamEncrypt_framed v
    spSafe := withStackScratch_spSafe (by decide) (streamEncrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamDecrypt v.callees)
    stack := 2632
    verified := streamDecrypt_framed v
    spSafe := withStackScratch_spSafe (by decide) (streamDecrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.AesGcm.X86.streamFinish v.callees)
    stack := 2628
    verified := streamFinish_framed v
    spSafe := withStackScratch_spSafe (by decide) (streamFinish_spSafe v)
    features := v.features },
  Spec.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamVerify v.callees)
    stack := 2632
    verified := streamVerify_framed v
    spSafe := withStackScratch_spSafe (by decide) (streamVerify_spSafe v)
    features := v.features },
  Spec.Gcm.sealApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.«seal» v.callees)
    stack := 2632
    verified := seal_framed v
    spSafe := withStackScratch_spSafe (by decide) (seal_spSafe v)
    features := v.features },
  Spec.Gcm.openApi.artifact X86.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesGcm.X86.«open» v.callees)
    stack := 2636
    verified := open_framed v
    spSafe := withStackScratch_spSafe (by decide) (open_spSafe v)
    features := v.features }]

/-- How `seal_gather` is built. -/
def gatherNote (fn : String) : String :=
  "This implementation copies the slices, a word at a time, one after the other to `dst`, and \
    encrypts them there in place with `" ++ fn ++ "`."

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact X86.target {
    suffix := v.suffix
    notes := [gatherNote (Gather.sealFn v).name]
    code := Impl.AesGcm.X86.SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code
    stack := 2684
    verified := Gather.sealGather_verified (Gather.sealFn v)
    spSafe := Gather.sealGather_spSafe v
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl ++ artifactsGather v.impl

end VG.Generic.AesGcm.X86.AesGcm
