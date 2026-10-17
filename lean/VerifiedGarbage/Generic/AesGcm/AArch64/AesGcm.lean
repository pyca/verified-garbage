module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Prepared
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPrepared
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM (NIST SP 800-38D) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_expand_key_scratch`, `vg_aes_ctr32` and `vg_ghash`,
are emitted once for each combination (`Variants/AesGcm/AArch64/`), named with
its suffix (e.g. `vg_aes_gcm_seal_aes`), and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; these artifacts are made from each function's `Api` (in
`Spec/`, reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function needs the CPU features of the implementations it calls:
`init` calls only AES's, `stream_init` and `stream_aad` only GHASH's.

The functions' calls (`bl`) keep the return address in `x30`, which they
save in the working space. `seal` and `open` read their last arguments from
the stack. Every function keeps its working space in a frame of 2560 bytes,
or, for `seal` and `open`, 2576 and 2592 bytes that also hold a copy of
their stack arguments.
-/

@[expose] public section

namespace VG.Generic.AesGcm.AArch64.AesGcm

open VG.Proof.AesGcm.AArch64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and hashes with `" ++ v.gh.fn.name ++ "`."

/-- How `seal` takes the records of TLS, for the implementations with PMULL. -/
def fastNote (v : GcmImpl) : List String :=
  if v.gh.pmull then ["For a 12-byte nonce and at most 16 bytes of additional data (TLS records), it computes \
    the hash subkey's `H · x⁻¹` once and multiplies the additional data, the last bytes of the ciphertext and \
    the lengths block into the hash with PMULL in registers, calling `" ++ v.gh.fn.name ++ "` once, on the \
    whole blocks of the ciphertext."] else []

/-- How `open` takes the records of TLS, for the implementations with PMULL. -/
def fastOpenNote (v : GcmImpl) : List String :=
  if v.gh.pmull then ["For a 12-byte nonce and at most 16 bytes of additional data (TLS records), it computes \
    the tag as `seal` does on that path, calling `" ++ v.gh.fn.name ++ "` once, on the whole blocks of the \
    ciphertext, and decrypts only if it matches."] else []

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (Impl.AesGcm.AArch64.init v.callees)
    stack := 2560
    verified := init_framed v
    features := v.ctr.features },
  Spec.Gcm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v] ++ fastNote v
    code := Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)
    stack := 2576
    verified := sealCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features },
  Spec.Gcm.openApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v] ++ fastOpenNote v
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v)
    stack := 2592
    verified := openCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features },
  Spec.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x4 (Impl.AesGcm.AArch64.streamInit v.callees)
    stack := 2560
    verified := streamInit_framed v
    features := v.gh.features },
  Spec.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x5 (Impl.AesGcm.AArch64.streamAad v.callees)
    stack := 2560
    verified := streamAad_framed v
    features := v.gh.features },
  Spec.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (Impl.AesGcm.AArch64.streamEncrypt v.callees)
    stack := 2560
    verified := streamEncrypt_framed v
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (Impl.AesGcm.AArch64.streamDecrypt v.callees)
    stack := 2560
    verified := streamDecrypt_framed v
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x6
      (Impl.AesGcm.AArch64.streamFinish v.callees)
    stack := 2560
    verified := streamFinish_framed v
    features := v.features },
  Spec.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7
      (Impl.AesGcm.AArch64.streamVerify v.callees)
    stack := 2560
    verified := streamVerify_framed v
    features := v.features }]

/-- What `vg_aes_gcm_seal_gather` does: it calls `vg_aes_gcm_seal`. -/
def gatherNote (fn : String) : String :=
  "This implementation copies the slices, 16 bytes at a time, one after the other to `dst`, and \
    encrypts them there in place with `" ++ fn ++ "`."

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [gatherNote (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV).fn.name]
    code := Impl.AesGcm.AArch64.SealGather.sealGather (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV).fn
    stack := 2592
    verified := Proof.AesGcm.AArch64.Gather.sealGather_verified (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV)
    features := v.features }]

/-- How `vg_aes_gcm_derive_prepared8` computes the powers. -/
def preparedNote : String :=
  "This implementation copies the key context, then computes `H' = H · x⁻¹` as `vg_ghash_aes` does, then \
    each even power `H'²ᵏ` by squaring `H'ᵏ`, read back from the context, and each odd power by one \
    multiplication by `H'`; `preparedPower(Hᵏ)` is `Hᵏ · x⁻¹`, so each power is stored as it is computed."

/-- How `vg_aes_gcm_seal_prepared8` uses the prepared context. -/
def sealPreparedNote (v : GcmImpl) (gp : GhashPreparedImpl) : String :=
  "For a 12-byte nonce and at most 16 bytes of additional data (TLS records), it computes the hash \
    subkey's `H · x⁻¹` once and multiplies the additional data, the last bytes of the ciphertext and the \
    lengths block into the hash with PMULL in registers, calling `" ++ gp.fn.name ++ "` once, on the whole \
    blocks of the ciphertext, which reads the powers of `H` from the context. Otherwise it reads only the \
    context's first 256 bytes, as `" ++ Spec.Gcm.sealApi.name ++ v.suffix ++ "` does."

/-- How `vg_aes_gcm_open_prepared8` uses the prepared context. -/
def openPreparedNote (v : GcmImpl) (gp : GhashPreparedImpl) : String :=
  "For a 12-byte nonce and at most 16 bytes of additional data (TLS records), it computes the tag as \
    `" ++ Spec.Gcm.sealPrepared8Api.name ++ v.suffix ++ "` does, calling `" ++ gp.fn.name ++ "` once, on the \
    whole blocks of the ciphertext, and decrypts only if it matches. Otherwise it reads only the context's \
    first 256 bytes, as `" ++ Spec.Gcm.openApi.name ++ v.suffix ++ "` does."

/-- `vg_aes_gcm_seal_prepared8` and `vg_aes_gcm_open_prepared8`, calling `gp`
on the path for TLS records, and `vg_aes_gcm_seal_gather_prepared8`, calling
the former. -/
def sealPreparedArtifacts (v : GcmImpl) (gp : GhashPreparedImpl) : List Artifact :=
  let F := Proof.AesGcm.AArch64.sealPreparedFn v gp Proof.Gcm.AArch64.Pmull.mulV_keyV
  [Spec.Gcm.sealPrepared8Api.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v, sealPreparedNote v gp]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2576 1
      (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn)
    stack := 2576
    verified := Fast.sealPrepared_framed v gp Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features },
  Spec.Gcm.sealGatherPrepared8Api.artifact AArch64.target {
    suffix := v.suffix
    notes := [gatherNote F.fn.name]
    code := Impl.AesGcm.AArch64.SealGather.sealGather F.fn
    stack := 2592
    verified := Proof.AesGcm.AArch64.Gather.sealGatherPrepared_verified F
    features := v.features },
  Spec.Gcm.openPrepared8Api.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v, openPreparedNote v gp]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2
      (Impl.AesGcm.AArch64.Fast.openWith v.callees gp.fn)
    stack := 2592
    verified := Fast.openPrepared_framed v gp Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features }]

/-- The functions with a prepared key context, for the implementations with PMULL. -/
def artifactsPrepared (v : GcmImpl) : List Artifact :=
  if v.gh.pmull then [
    Spec.Gcm.derivePrepared8Api.artifact AArch64.target {
      suffix := v.suffix
      notes := [preparedNote]
      code := Impl.AesGcm.AArch64.Prepared.derive
      verified := derive_verified Proof.Gcm.AArch64.Pmull.prepPow
      features := ["aes"] }] ++ ((v.gh.prepared.map (sealPreparedArtifacts v)).getD [])
  else []

/-- How the `*_with_powers` functions use the powers. -/
def withPowersNote (v : GcmImpl) (g : GhashWithImpl) (name : String) : String :=
  "For a 12-byte nonce and at most 16 bytes of additional data (TLS records), it computes the tag as `" ++
    name ++ v.suffix ++ "` does, calling `" ++ g.fn.name ++ "` once, on the whole blocks of the text, which reads \
    the powers of `H` from `pw`. Otherwise it never reads `pw`, and computes as `" ++ name ++ v.suffix ++ "` does."

/-- `vg_aes_gcm_seal_with_powers` and `vg_aes_gcm_open_with_powers`, calling
`g` on the path for TLS records. -/
def withPowersArtifacts (v : GcmImpl) (g : GhashWithImpl) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v, withPowersNote v g Spec.Gcm.sealApi.name]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2
      (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn)
    stack := 2592
    verified := Fast.sealPw_framed v g Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v, withPowersNote v g Spec.Gcm.openApi.name]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 3
      (Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn)
    stack := 2592
    verified := Fast.openPw_framed v g Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ artifactsGather v.impl ++ artifactsPrepared v.impl ++
    (v.impl.gh.withPowers.map (withPowersArtifacts v.impl)).getD []

end VG.Generic.AesGcm.AArch64.AesGcm
