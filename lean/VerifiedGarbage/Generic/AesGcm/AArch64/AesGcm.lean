module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Init
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
public import VerifiedGarbage.Proof.AesGcm.CtxFrame
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Final
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Instances
import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Final
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.SealGather

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
`init` calls only AES's, `stream_init` and `stream_aad` only GHASH's. With
the interleaved loops (`GcmImpl.stitch`), the functions with the powers also
need `FEAT_SHA3`.

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

/-- How the functions with the powers take the whole chunks of 128 bytes of a
TLS record, with the interleaved loops. -/
def stitchNote (v : GcmImpl) : List String :=
  if v.stitch then ["With the interleaved loops, it encrypts or decrypts the first 128 ⌊n / 128⌋ bytes of the \
    text and hashes them eight blocks at a time, in one loop that interleaves the AES rounds with the PMULL \
    products and their reduction (with `eor3`, which needs `FEAT_SHA3`), from a table of the powers, and \
    hashes the rest's whole blocks with the call."] else []

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
  "This implementation copies the slices one after the other to `dst`, 16 bytes at a time and then \
    the last bytes of each eight, four and one at a time, and encrypts them there in place with `" ++
    fn ++ "`."

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [gatherNote (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV).fn.name]
    code := Impl.AesGcm.AArch64.SealGather.sealGather (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV).fn
    stack := 2592
    verified := Proof.AesGcm.AArch64.Gather.sealGather_verified (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV)
    features := v.features }]

/-- How the `*_with_powers` functions use the powers. -/
def withPowersNote (v : GcmImpl) (g : GhashWithImpl) (name : String) : String :=
  "For a 12-byte nonce and at most 16 bytes of additional data (TLS records), it computes the tag as `" ++
    name ++ v.suffix ++ "` does, calling `" ++ g.fn.name ++ "` once, on the whole blocks of the text, which reads \
    the powers of `H` from `pw`. Otherwise it never reads `pw`, and computes as `" ++ name ++ v.suffix ++ "` does."

/-- How the interleaved `*_with_powers` functions take a short TLS record. -/
def shortNote (v : GcmImpl) (isSeal : Bool) : List String :=
  if v.stitch then ["On the path for TLS records, a text of " ++
    (if isSeal then "17 to " else "at most ") ++ toString Impl.AesGcm.AArch64.Stitch.shortMax ++
    " bytes is " ++ (if isSeal then "sealed" else "opened") ++ " without the call: its blocks, the additional data \
    and the lengths are laid out in `work`, encrypted in one pass of the loop's AES rounds and hashed in one \
    pass of its products, from the table of the powers read from `pw`."] else []

/-- `vg_aes_gcm_seal_with_powers` and `vg_aes_gcm_open_with_powers`, calling
`g` on the path for TLS records, and `vg_aes_gcm_seal_gather_with_powers`,
calling that `vg_aes_gcm_seal_with_powers`. -/
def withPowersArtifacts (v : GcmImpl) (g : GhashWithImpl) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v, withPowersNote v g Spec.Gcm.sealApi.name] ++ stitchNote v ++ shortNote v true
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g)
    stack := 2592
    verified := sealPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g
    features := v.stitchFeatures },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [note v, withPowersNote v g Spec.Gcm.openApi.name] ++ stitchNote v ++ shortNote v false
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g)
    stack := 2592
    verified := openPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g
    features := v.stitchFeatures },
  Spec.Gcm.sealGatherWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [gatherNote (Spec.Gcm.sealWithPowersApi.name ++ v.suffix)]
    code := Impl.AesGcm.AArch64.SealGather.sealGatherPw
      (Proof.AesGcm.AArch64.sealPwFn v g Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok).fn
    stack := 2624
    verified := Proof.AesGcm.AArch64.GatherPw.sealGatherPw_verified
      (Proof.AesGcm.AArch64.sealPwFn v g Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok)
    features := v.stitchFeatures }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ artifactsGather v.impl ++
    (v.impl.gh.withPowers.map (withPowersArtifacts v.impl)).getD []

end VG.Generic.AesGcm.AArch64.AesGcm
