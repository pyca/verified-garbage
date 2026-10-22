module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.Framework.X86_64.Registration

/-!
# AES-GCM (NIST SP 800-38D) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_expand_key_scratch`, `vg_aes_ctr32` and `vg_ghash`,
are emitted once for each combination (`Variants/AesGcm/X86_64/`), named with
its suffix (e.g. `vg_aes_gcm_seal_aesni_pclmul`), and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; these artifacts are made from each function's `Api` (in
`Spec/`, reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function needs the CPU features of the implementations it calls:
`init` calls only AES's, `stream_init` and `stream_aad` only GHASH's (so
their `_aesni` or `_pclmul` instances are the baseline code under another
name, which keeps every instance of a combination callable together), and
`stream_finish` and `stream_verify` only both's (they do not call the
interleaved loops, whose features `GcmImpl.features` adds).

`seal`, `open`, `stream_encrypt` and `stream_decrypt` encrypt or decrypt
and absorb the whole blocks of the data in one call of the instance of
`vg_aes_gcm_encrypt_blocks` or `vg_aes_gcm_decrypt_blocks` for the same
combination, which interleaves the two for the implementations that allow
it (`GcmImpl.stitch`). With the loops on 512-bit registers, `seal` and
`open` instead take a short path, without calls, for a 12-byte nonce and
fewer than 32 blocks of additional data and text, with some text or more
than 16 bytes of additional data (`GcmImpl.short`,
`Impl/AesGcm/X86_64/Short.lean`).

The code of `init`, `stream_init`, `stream_aad`, `stream_finish` and
`stream_verify` uses 8 bytes of stack: the return address of a call of
`vg_aes_expand_key_scratch`, `vg_aes_ctr32` or `vg_ghash`, which make no calls. That
of `seal`, `open`, `stream_encrypt` and `stream_decrypt` uses 24: the
argument they pass on the stack, the return address of their call of
`vg_aes_gcm_encrypt_blocks` or `vg_aes_gcm_decrypt_blocks`, and that of its
calls. Every function keeps its working space in a frame on the stack: 2568
bytes for `init`, `stream_init` and `stream_aad` (`Verified.stackScratch`),
and for the others, whose working space is their last argument passed on the
stack, a frame that also holds a copy of their other stack arguments
(`Verified.stackArgScratch`): 2576 bytes for `stream_finish`, 2584 for
`stream_verify`, `stream_encrypt` and `stream_decrypt`, 2600 for `seal` and
2608 for `open`.

The variants whose interleaved loops can read the powers `H¹ … H⁴⁸` of the
hash subkey from a key context of `vg_aes_gcm_init_precomputed`
(`Spec/Gcm/Precomputed.lean`) instead of computing them on every call
(`StitchPart.pieceP`, so far only `StitchZP`'s, on 512-bit registers) also
have cached-context functions: `_prepared` (`artifactsR`) when their loops
support prepared pairs (`StitchPart.pieceR`), otherwise `_precomputed`
(`artifactsP`). Prepared initialization converts the powers once; its loops
load the encoded pairs directly and align their working tables to 64 bytes. The precomputed functions are: `init_precomputed`, which
is `init` followed by the powers, computed one at a time with `vg_ghash`
(`InitP.lean`), and `seal`, `open`, `stream_encrypt`, `stream_decrypt` and
the whole-blocks functions for that key context, with the same stack and
frames as theirs.

Every variant also encrypts out of place (`Spec/Gcm/OutOfPlace.lean`):
`encrypt_blocks_to` with its own out-of-place interleaved loops where the
variant has them (`StitchPart.toPart`), and otherwise by copying the blocks
and calling `encrypt_blocks`, in 24 bytes of stack; and `stream_encrypt_to`,
calling `encrypt_blocks_to` for the whole blocks when the text so far ends a
block and `stream_encrypt` for the rest, after copying it, in a frame of 2232
bytes for its 2192 bytes of working space (`StreamTo/Verified.lean`), and
4856 bytes of stack in all; and `seal_gather`, from a list of slices: for a
text shorter than `copyBelow` bytes or whose first slice holds all its whole
blocks, by copying the slices to the output and calling `seal` there (with
the same key context), or, from a first slice holding all the whole blocks
and at least `splitFrom` bytes, by copying the slices after it and calling
`seal_split`, and otherwise by
calling `stream_init`, `stream_aad`, `stream_encrypt_to` once for each slice
and `stream_finish` (`Impl/AesGcm/X86_64/SealGather.lean`), in a frame of
240 bytes for its 184 bytes of working space (`Gather/Verified.lean`), and
5128 bytes of stack in all.
-/

@[expose] public section

namespace VG.Generic.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and hashes with `" ++ v.gh.fn.name ++ "`."

/-- How an instance of `seal` or `open` works, besides `note`. -/
def shortNote (v : GcmImpl) : List String :=
  if v.short then
    ["For a 12-byte nonce and fewer than 32 blocks of additional data and text, with some text or \
      more than 16 bytes of additional data, this implementation computes just the powers of the hash \
      subkey and the keystream they need, on 512-bit registers, without calls."]
  else []

/-- How an instance of `seal_prepared` or `open_prepared` works, besides `note`. -/
def shortNoteP (v : GcmImpl) : List String :=
  if v.short then
    ["For a 12-byte nonce and fewer than 32 blocks of additional data and text, with some text or \
      more than 16 bytes of additional data, this implementation copies the powers of the hash subkey \
      from the key context and computes just the keystream it needs, on 512-bit registers, without calls."]
  else []

/-- How an instance of `open_prepared` works, besides `note` and `shortNoteP`. -/
def openFastNote (v : GcmImpl) : List String :=
  if v.short then
    ["For a 12-byte nonce, at most 16 bytes of additional data and at least 256 bytes of text, this \
      implementation multiplies the additional data by the prepared power of the hash subkey in the key \
      context, and computes the tag from the prepared powers in the key context, without calls."]
  else []

/-- How an instance of `seal` ends, besides `note` and `shortNote`. -/
def finNote (v : GcmImpl) : List String :=
  if v.fin then
    ["After the whole blocks, this implementation encrypts the bytes left and computes the tag without \
      calls, with AES-NI and PCLMULQDQ."]
  else []

/-- How an instance of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks` works. -/
def blocksNote (v : GcmImpl) (enc : Bool := false) : String :=
  if v.stitch.isSome then
    "This implementation interleaves the AES rounds of 16 blocks at a time with GHASH's \
      multiplications of the 16 blocks before them, from the powers of the hash subkey it \
      computes in `scratch`, and handles the rest" ++
      (if enc && v.stitch.any (·.full) then " in the same pass when there are at least 16 blocks, \
        and otherwise" else "") ++ " with `" ++ v.ctr.callee.name ++ "` and `" ++
      v.gh.fn.name ++ "`."
  else
    "This implementation calls `" ++ v.ctr.callee.name ++ "` and `" ++ v.gh.fn.name ++ "`."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.encryptBlocksApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [blocksNote v true]
    code := v.callees.enc.code
    stack := 8
    verified := encryptBlocks_verified v v.stitch
    spSafe := encryptBlocks_spSafeB v v.stitch
    features := v.features },
  Spec.Gcm.decryptBlocksApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [blocksNote v]
    code := v.callees.dec.code
    stack := 8
    verified := decryptBlocks_verified v v.stitch
    spSafe := decryptBlocks_spSafeB v v.stitch
    features := v.features },
  Spec.Gcm.initApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init v.callees)
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := (v.ctr.features ++ v.key.features).dedup },
  Spec.Gcm.sealApi.artifact X86_64.target {
    suffix := v.suffix
    notes := note v :: shortNote v ++ finNote v
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees)
    stack := 2624
    verified := sealSel_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkB)
    features := v.features },
  Spec.Gcm.openApi.artifact X86_64.target {
    suffix := v.suffix
    notes := note v :: shortNote v
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees)
    stack := 2632
    verified := openSel_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkB)
    features := v.features },
  Spec.Gcm.streamInitApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit v.callees)
    stack := 2576
    verified := streamInit_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamInit_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamAadApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad v.callees)
    stack := 2576
    verified := streamAad_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamAad_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.callees)
    stack := 2608
    verified := streamEncrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.callees)
    stack := 2608
    verified := streamDecrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)
    stack := 2584
    verified := streamFinish_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup },
  Spec.Gcm.streamVerifyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify v.callees)
    stack := 2592
    verified := streamVerify_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup }]

/-- How an instance of `vg_aes_gcm_encrypt_blocks_precomputed` or
`_decrypt_blocks_precomputed` works. -/
def blocksNoteP (v : GcmImpl) : String :=
  "This implementation interleaves the AES rounds of 16 blocks at a time with GHASH's \
    multiplications of the 16 blocks before them, from the powers of the hash subkey it \
    reads from the key context, and handles the rest with `" ++ v.ctr.callee.name ++ "` and `" ++
    v.gh.fn.name ++ "`."

/-- How an instance of `vg_aes_gcm_init_precomputed` works. -/
def initNoteP (v : GcmImpl) : String :=
  note v ++ " It computes the powers of the hash subkey with `" ++ v.gh.fn.name ++ "`, one at a time."

/-- The `_precomputed` artifacts calling the implementations `v`. -/
def artifactsP (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [initNoteP v]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.initPrecomputed v.callees)
    stack := 2576
    verified := initP_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (initP_spSafe v)
    features := (v.ctr.features ++ v.key.features ++ v.gh.features).dedup },
  Spec.Gcm.encryptBlocksPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [blocksNoteP v]
    code := v.blkP.enc.code
    stack := 8
    verified := encryptBlocksP_verified v v.stitchP
    spSafe := v.blkP.encSp
    features := v.features },
  Spec.Gcm.decryptBlocksPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [blocksNoteP v]
    code := v.blkP.dec.code
    stack := 8
    verified := decryptBlocksP_verified v v.stitchP
    spSafe := v.blkP.decSp
    features := v.features },
  Spec.Gcm.sealPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := note v :: shortNote v ++ finNote v
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP))
    stack := 2624
    verified := sealSelP_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkP)
    features := v.features },
  Spec.Gcm.openPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := note v :: shortNote v
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk v.blkP))
    stack := 2632
    verified := openSelP_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkP)
    features := v.features },
  Spec.Gcm.streamEncryptPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.withBlk v.blkP))
    stack := 2608
    verified := streamEncryptP_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v v.blkP)
    features := v.features },
  Spec.Gcm.streamDecryptPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.withBlk v.blkP))
    stack := 2608
    verified := streamDecryptP_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v v.blkP)
    features := v.features }]

/-- How an instance of `vg_aes_gcm_encrypt_blocks_to` works. -/
def blocksToNote (loops : Bool) (blk : String) : String :=
  if loops then
    "This implementation encrypts the first `16 ⌊n / 16⌋` blocks from `src` to `dst` with \
      AES rounds of 16 blocks at a time interleaved with GHASH's multiplications of the 16 \
      blocks before them, from the powers of the hash subkey it computes in `scratch`; it \
      copies the rest to `dst` and encrypts them there with `" ++ blk ++ "`."
  else
    "This implementation copies the blocks to `dst` and encrypts them there with `" ++ blk ++
      "`."

/-- How an instance of `vg_aes_gcm_stream_encrypt_to` works. -/
def streamToNote (blk enc : String) : String :=
  "If the text so far ends inside a block, this implementation first copies the bytes of the \
    input that end it to `dst` and encrypts them there with `" ++ enc ++ "`; then it encrypts the \
    whole blocks of the rest of the input from `src` to `dst` with `" ++ blk ++ "`; it copies what \
    is left to `dst` and encrypts it there with `" ++ enc ++ "`."

/-- `vg_aes_gcm_encrypt_blocks_to` and `vg_aes_gcm_stream_encrypt_to` calling
the implementations `v`, and the `_precomputed` ones if its loops read the
powers from the key context. -/
def artifactsTo (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.encryptBlocksToApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [blocksToNote v.stitchTo.isSome v.impl.blkB.enc.name]
    code := Impl.AesGcm.X86_64.BlocksTo.encrypt v.impl.blkB.enc (v.stitchTo.map (·.enc)) false (encFullTo v.stitchTo)
    stack := 24
    verified := encryptBlocksTo_verified v.impl.blkB v.stitchTo
    spSafe := encryptTo_spSafe v.stitchTo v.impl.blkB
    features := v.impl.features },
  Spec.Gcm.streamEncryptToApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [streamToNote (blkTo v).fn.name (encFn v.impl).fn.name]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2232 3
      (Impl.AesGcm.X86_64.StreamTo.encrypt (blkTo v).fn (encFn v.impl).fn)
    stack := 4856
    verified := StreamTo.streamEncryptTo_framed (blkTo v) (encFn v.impl)
    spSafe := X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkTo v) (encFn v.impl))
    features := v.impl.features }] ++
  if v.impl.stitchP.isSome && v.stitchR.isNone then
    [Spec.Gcm.encryptBlocksToPrecomputedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [blocksToNote v.stitchToP.isSome v.impl.blkP.enc.name]
      code := Impl.AesGcm.X86_64.BlocksTo.encrypt v.impl.blkP.enc (v.stitchToP.map (·.enc)) false (encFullTo v.stitchToP)
      stack := 24
      verified := encryptBlocksToP_verified v.impl.blkP v.stitchToP
      spSafe := encryptTo_spSafe v.stitchToP v.impl.blkP
      features := v.impl.features },
    Spec.Gcm.streamEncryptToPrecomputedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [streamToNote (blkToP v).fn.name (encFnP v.impl).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToP v).fn (encFnP v.impl).fn)
      stack := 4856
      verified := StreamTo.streamEncryptToP_framed (blkToP v) (encFnP v.impl)
      spSafe := X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToP v) (encFnP v.impl))
      features := v.impl.features }]
  else []

/-- How an instance of `vg_aes_gcm_seal_gather` works: below `t` bytes, or
when its first slice holds all the whole blocks, it takes the short path:
`splitName` (`vg_aes_gcm_seal_split`) if that slice also holds at least `ts`
bytes, and otherwise `sealName` (`vg_aes_gcm_seal`) on the whole text
copied; otherwise `enc`. -/
def gatherNote (t ts : Nat) (sealName splitName enc : String) : String :=
  "When the text is shorter than " ++ toString t ++ " bytes, or its first slice holds all its whole \
    blocks, this implementation takes a short path. If that slice holds all the whole blocks and at least " ++
    toString ts ++ " bytes, it copies the slices after it to the output after its length and encrypts the \
    text with `" ++ splitName ++ "`, from the first slice where it is and the rest in the output; \
    otherwise it copies all the slices to the output and encrypts the text there with `" ++ sealName ++
    "`. Otherwise, it runs the streaming functions on a state of its own: it absorbs the additional data, \
    padded with zeros to a whole block (as GHASH pads it), and encrypts each slice from where it is to the \
    output with `" ++ enc ++ "`."

/-- How `vg_aes_gcm_seal_gather_prepared` takes a TLS record's text, before
`gatherNote`'s paths. -/
def tlsNote (splitName : String) (long : Bool) : String :=
  "A text of a TLS record (a 12-byte nonce, at most 16 bytes of additional data, and one or two slices, \
    the second ending at most 16 bytes after the first's whole blocks) is sealed first, from the entry: the \
    second slice, if any, is copied to the output after the first, and the text is encrypted with `" ++
    splitName ++ "` from the first slice where it is" ++
    (if long then ", if that slice holds at least 256 bytes"
      else ", unless the text is at least 256 bytes long and that slice shorter") ++ "."

/-- `vg_aes_gcm_seal_gather` calling the implementations `v`, and the
`_precomputed` one if its loops read the powers from the key context. -/
def artifactsGather (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.sealGatherApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [gatherNote (copyBelow v) (splitFrom v) (sealFn v.impl).fn.name (splitFn v).fn.name (toFn v).fn.name]
    code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn
        (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
    stack := 5128
    verified := Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v)
      (finFn v.impl)
    spSafe := X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v)
        (finFn v.impl))
    features := v.impl.features }] ++
  if v.impl.stitchP.isSome && v.stitchR.isNone then
    [Spec.Gcm.sealGatherPrecomputedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [gatherNote (copyBelow v) (splitFrom v) (sealFnP v.impl).fn.name (splitFnP v).fn.name (toFnP v).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnP v).quick (shortFnP v).fast (shortFnP v).test
        (shortFnP v).code (initFn v.impl).fn
          (aadFn v.impl).fn (toFnP v).fn (finFn v.impl).fn)
      stack := 5128
      verified := Gather.sealGatherP_framed (shortFnP v) (initFn v.impl) (aadFn v.impl)
        (toFnP v) (finFn v.impl)
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFnP v) (initFn v.impl) (aadFn v.impl) (toFnP v)
          (finFn v.impl))
      features := v.impl.features }]
  else []

def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.encryptBlocksPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [blocksNoteP v.impl]
    code := (blkR v).enc.code
    stack := 8
    verified := encryptBlocksPrepared_verified v.impl v.stitchR
    spSafe := (blkR v).encSp
    features := v.impl.features },
  Spec.Gcm.decryptBlocksPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [blocksNoteP v.impl]
    code := (blkR v).dec.code
    stack := 8
    verified := decryptBlocksPrepared_verified v.impl v.stitchR
    spSafe := (blkR v).decSp
    features := v.impl.features },
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := note v.impl :: shortNoteP v.impl ++ finNote v.impl
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR v)))
    stack := 2624
    verified := sealSelPrepared_framed v.impl (blkR v) Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR v))
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := note v.impl :: shortNoteP v.impl ++ openFastNote v.impl
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR v)))
    stack := 2632
    verified := openSelPrepared_framed v.impl (blkR v) Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR v))
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [note v.impl]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v)))
    stack := 2608
    verified := streamEncryptPrepared_framed v.impl (blkR v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR v))
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [note v.impl]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR v)))
    stack := 2608
    verified := streamDecryptPrepared_framed v.impl (blkR v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v))
    features := v.impl.features }]

def artifactsToR (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.encryptBlocksToPreparedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [blocksToNote v.stitchToR.isSome (blkR v).enc.name]
      code := Impl.AesGcm.X86_64.BlocksTo.encrypt (blkR v).enc (v.stitchToR.map (·.enc)) true (encFullTo v.stitchToR)
      stack := 24
      verified := encryptBlocksToPrepared_verified (blkR v) v.stitchToR
      spSafe := encryptTo_spSafe v.stitchToR (blkR v)
      features := v.impl.features },
    Spec.Gcm.streamEncryptToPreparedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [streamToNote (blkToR v).fn.name (encFnR v).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToR v).fn (encFnR v).fn)
      stack := 4856
      verified := StreamTo.streamEncryptToPrepared_framed (blkToR v) (encFnR v)
      spSafe := X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToR v) (encFnR v))
      features := v.impl.features }]

def artifactsGatherR (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [tlsNote (splitFnR v).fn.name (tlsLong v),
        gatherNote (copyBelow v) (splitFrom v) (sealFnR v).fn.name (splitFnR v).fn.name (toFnR v).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnR v).fn
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnR v).quick (shortFnR v).fast (shortFnR v).test
            (shortFnR v).code (initFn v.impl).fn (aadFn v.impl).fn (toFnR v).fn (finFn v.impl).fn))
      stack := 5128
      verified := Gather.sealGatherPrepared_framed (shortFnR v) (initFn v.impl) (aadFn v.impl)
        (toFnR v) (finFn v.impl) (splitFnR v) (tlsLong v)
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.withFront_spAll (shortFnR v) (initFn v.impl) (aadFn v.impl) (toFnR v)
          (finFn v.impl) (splitFnR v) (tlsLong v))
      features := v.impl.features }]

def artifactsR16 (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.encryptBlocksPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [blocksNoteP v.impl]
    code := (blkR16 v).enc.code
    stack := 8
    verified := encryptBlocksPrepared16_verified v.impl v.stitchR16
    spSafe := (blkR16 v).encSp
    features := v.impl.features },
  Spec.Gcm.decryptBlocksPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [blocksNoteP v.impl]
    code := (blkR16 v).dec.code
    stack := 8
    verified := decryptBlocksPrepared16_verified v.impl v.stitchR16
    spSafe := (blkR16 v).decSp
    features := v.impl.features },
  Spec.Gcm.sealPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := note v.impl :: shortNoteP v.impl ++ finNote v.impl
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR16 v)))
    stack := 2624
    verified := sealSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short
    spSafe := X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR16 v))
    features := v.impl.features },
  Spec.Gcm.openPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := note v.impl :: shortNoteP v.impl ++ openFastNote v.impl
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR16 v)))
    stack := 2632
    verified := openSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short
    spSafe := X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR16 v))
    features := v.impl.features },
  Spec.Gcm.streamEncryptPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [note v.impl]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v)))
    stack := 2608
    verified := streamEncryptPrepared16_framed v.impl (blkR16 v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR16 v))
    features := v.impl.features },
  Spec.Gcm.streamDecryptPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [note v.impl]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR16 v)))
    stack := 2608
    verified := streamDecryptPrepared16_framed v.impl (blkR16 v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v))
    features := v.impl.features }]

def artifactsToR16 (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.encryptBlocksToPrepared16Api.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [blocksToNote v.stitchToR16.isSome (blkR16 v).enc.name]
      code := Impl.AesGcm.X86_64.BlocksTo.encrypt (blkR16 v).enc (v.stitchToR16.map (·.enc)) true (encFullTo v.stitchToR16)
      stack := 24
      verified := encryptBlocksToPrepared16_verified (blkR16 v) v.stitchToR16
      spSafe := encryptTo_spSafe v.stitchToR16 (blkR16 v)
      features := v.impl.features },
    Spec.Gcm.streamEncryptToPrepared16Api.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [streamToNote (blkToR16 v).fn.name (encFnR16 v).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToR16 v).fn (encFnR16 v).fn)
      stack := 4856
      verified := StreamTo.streamEncryptToPrepared16_framed (blkToR16 v) (encFnR16 v)
      spSafe := X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToR16 v) (encFnR16 v))
      features := v.impl.features }]

def artifactsGatherR16 (v : GcmVariant) (r : R16 v) : List Artifact :=
  [Spec.Gcm.sealGatherPrepared16Api.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [tlsNote (splitFnR16 v r.onePass).fn.name (tlsLong v),
        gatherNote (copyBelow v) (splitFrom v) (sealFnR16 v r.short).fn.name (splitFnR16 v r.onePass).fn.name (toFnR16 v).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnR16 v r.onePass).fn
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnR16 v r.short r.onePass).quick (shortFnR16 v r.short r.onePass).fast (shortFnR16 v r.short r.onePass).test
            (shortFnR16 v r.short r.onePass).code (initFn v.impl).fn (aadFn v.impl).fn (toFnR16 v).fn (finFn v.impl).fn true))
      stack := 5128
      verified := Gather.sealGatherPrepared16_framed (shortFnR16 v r.short r.onePass) (initFn v.impl) (aadFn v.impl)
        (toFnR16 v) (finFn v.impl) (splitFnR16 v r.onePass) (tlsLong v)
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.withFront_spAll (shortFnR16 v r.short r.onePass) (initFn v.impl) (aadFn v.impl) (toFnR16 v)
          (finFn v.impl) (splitFnR16 v r.onePass) (tlsLong v) true)
      features := v.impl.features }]

/-- How an instance of `vg_aes_gcm_seal_split` works. -/
def splitNote (blk : String) : String :=
  "This implementation encrypts the whole blocks at `src` straight to `dst` with `" ++ blk ++ "`, copies \
    the bytes of `src` left after them to `dst`, and goes on as `vg_aes_gcm_seal` does from there: it \
    encrypts the rest in place, then the bytes left after its whole blocks, and computes the tag."

/-- How an instance of `seal_split_prepared` works, besides `note` and `splitNote`. -/
def fastNote (v : GcmImpl) : List String :=
  if v.short then
    ["For a 12-byte nonce, at most 16 bytes of additional data and at least 256 bytes of text, this \
      implementation multiplies the additional data by the prepared power of the hash subkey in the key \
      context, without calls."]
  else []

/-- `vg_aes_gcm_seal_split` of a variant, and the `_precomputed` or
`_prepared` one for the key context its loops read the powers from. -/
def artifactsSplit (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.sealSplitApi.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [note v.impl, splitNote (blkTo v).fn.name]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2616 5
      (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMid (v.impl.withBlk v.impl.blkB) (blkTo v).fn))
    stack := 2672
    verified := Split.sealSplit_framed v.impl Short.shortFacts v.impl.blkB (blkTo v)
    spSafe := X86_64.withStackArgScratch_spSafe (Split.sealSplit_spSafe v.impl v.impl.blkB (blkTo v))
    features := v.impl.features }] ++
  (if v.impl.stitchP.isSome && v.stitchR.isNone then
    [Spec.Gcm.sealSplitPrecomputedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [note v.impl, splitNote (blkToP v).fn.name]
      code := Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMid (v.impl.withBlk v.impl.blkP) (blkToP v).fn))
      stack := 2672
      verified := Split.sealSplitP_framed v.impl Short.shortFacts v.impl.blkP (blkToP v)
      spSafe := X86_64.withStackArgScratch_spSafe (Split.sealSplit_spSafe v.impl v.impl.blkP (blkToP v))
      features := v.impl.features }]
  else []) ++
  (if v.stitchR.isSome && v.r16.isNone then
    [Spec.Gcm.sealSplitPreparedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      notes := [note v.impl, splitNote (blkToR v).fn.name] ++ fastNote v.impl
      code := Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR v)) (blkToR v).fn))
      stack := 2672
      verified := Split.sealSplitPrepared_framed v.impl (blkR v) (blkToR v) Short.shortFacts
      spSafe := X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR v) (blkToR v))
      features := v.impl.features }]
  else [])

/-- `vg_aes_gcm_seal_split_prepared16` of a variant whose loops read only the
first 16 powers. -/
def artifactsSplitR16 (v : GcmVariant) (r : R16 v) : List Artifact :=
  [Spec.Gcm.sealSplitPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    notes := [note v.impl, splitNote (blkToR16 v).fn.name] ++ fastNote v.impl
    code := Impl.StackScratch.X86_64.withStackArgScratch 2616 5
      (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR16 v)) (blkToR16 v).fn))
    stack := 2672
    verified := Split.sealSplitPrepared16_framed v.impl (blkR16 v) (blkToR16 v) Short.shortFacts r.onePass
    spSafe := X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR16 v) (blkToR16 v))
    features := v.impl.features }]

/-- Artifacts propagate the context format supported by each variant: prepared
powers when available, otherwise raw precomputed powers. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ (if v.impl.stitchP.isSome && v.stitchR.isNone then artifactsP v.impl else []) ++ artifactsTo v ++
    artifactsGather v ++ artifactsSplit v ++
    (match v.r16 with
      | some r => artifactsR16 v r.down ++ artifactsToR16 v ++ artifactsGatherR16 v r.down ++ artifactsSplitR16 v r.down
      | none => if v.stitchR.isSome then artifactsR v ++ artifactsToR v ++ artifactsGatherR v else [])

end VG.Generic.AesGcm.X86_64.AesGcm
