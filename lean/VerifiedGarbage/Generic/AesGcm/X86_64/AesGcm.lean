import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.OkP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Ok
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Field
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified

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
have the `_precomputed` functions (`artifactsP`): `init_precomputed`, which
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
4856 bytes of stack in all; and `seal_gather`, from a list of slices, by
calling `stream_init`, `stream_aad`, `stream_encrypt_to` once for each slice
and `stream_finish` (`Impl/AesGcm/X86_64/SealGather.lean`), in a frame of
240 bytes for its 184 bytes of working space (`Gather/Verified.lean`), and
5128 bytes of stack in all.
-/

/-! The interleaved loops a variant names, with their proofs (which import the
algebra of `Proof/Gcm/Poly.lean`, so that the variants need not), and the
implementations a variant names, resolved. -/

namespace VG.Proof.AesGcm.X86_64

/-- The loops named `n` interleave counter mode and GHASH correctly. -/
theorem StitchName.ok : (n : StitchName) → Proof.Gcm.X86_64.Stitch.StitchOk n.enc n.dec
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZ.stitch_ok
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx.stitch_ok

/-- The loops `p` names, with their proof. -/
def StitchPart.impl (p : StitchPart) : StitchImpl :=
  ⟨p.suffix, p.features, p.name.enc, p.name.dec, p.name.ok, p.encP, p.decP⟩

/-- The loops named `n` for a key context of `vg_aes_gcm_init_precomputed`
interleave counter mode and GHASH correctly. -/
theorem StitchName.okP : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP n.decP
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok.toM _
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZP.stitchP_ok.toM
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx.stitch_ok.toM _

/-- The loops `p` names for a key context of `vg_aes_gcm_init_precomputed`,
with their proof, if they read the powers of the hash subkey from it. -/
def StitchPart.implP (p : StitchPart) : Option (StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.powers) :=
  p.pieceP.map fun q => ⟨p.name.encP, p.name.decP, p.name.okP, q.enc, q.dec⟩

/-- The out-of-place loops named `n` interleave counter mode and GHASH
correctly. -/
theorem StitchToName.ok : (n : StitchToName) → (M : Proof.Gcm.X86_64.Stitch.CtxMode) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM M n.enc
  | .vaesAvx512, M => Proof.Gcm.X86_64.StitchZTo.stitchTo_ok M

/-- The out-of-place loops named `n` for a key context of
`vg_aes_gcm_init_precomputed` interleave counter mode and GHASH correctly. -/
theorem StitchToName.okP : (n : StitchToName) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZTo.stitchToP_ok

/-- The out-of-place loops a variant names, with their proof. -/
def GcmVariant.stitchTo (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.base) :=
  (v.stitch.bind (·.toPart)).map fun p => ⟨p.name.enc, p.name.ok _, p.piece⟩

/-- The out-of-place loops a variant names for a key context of
`vg_aes_gcm_init_precomputed`, with their proof. -/
def GcmVariant.stitchToP (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.powers) :=
  (v.stitch.bind (·.toPart)).bind fun p => p.pieceP.map fun q => ⟨p.name.encP, p.name.okP, q.enc⟩

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl :=
  ⟨v.ctr, v.key, v.gh.impl, v.stitch.map StitchPart.impl, v.stitch.bind StitchPart.implP,
    v.stitch.any (·.name.short)⟩

end VG.Proof.AesGcm.X86_64

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

/-- How an instance of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks` works. -/
def blocksNote (v : GcmImpl) : String :=
  if v.stitch.isSome then
    "This implementation interleaves the AES rounds of 16 blocks at a time with GHASH's \
      multiplications of the 16 blocks before them, from the powers of the hash subkey it \
      computes in `scratch`, and handles the rest with `" ++ v.ctr.callee.name ++ "` and `" ++
      v.gh.fn.name ++ "`."
  else
    "This implementation calls `" ++ v.ctr.callee.name ++ "` and `" ++ v.gh.fn.name ++ "`."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  { Spec.Gcm.encryptBlocksApi with
    name := Spec.Gcm.encryptBlocksApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.encryptBlocksApi.doc (notes := [blocksNote v])
    code := v.callees.enc.code
    contract := Spec.Gcm.encryptBlocksContract X86_64.abi 8
    stack := 8
    verified := encryptBlocks_verified v v.stitch
    spSafe := encryptBlocks_spSafeB v v.stitch
    features := v.features },
  { Spec.Gcm.decryptBlocksApi with
    name := Spec.Gcm.decryptBlocksApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.decryptBlocksApi.doc (notes := [blocksNote v])
    code := v.callees.dec.code
    contract := Spec.Gcm.decryptBlocksContract X86_64.abi 8
    stack := 8
    verified := decryptBlocks_verified v v.stitch
    spSafe := decryptBlocks_spSafeB v v.stitch
    features := v.features },
  { Spec.Gcm.initApi with
    name := Spec.Gcm.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.initApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init v.callees)
    contract := Spec.Gcm.initContract X86_64.abi 2576
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (init_spSafe v)
    features := (v.ctr.features ++ v.key.features).dedup },
  { Spec.Gcm.sealApi with
    name := Spec.Gcm.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.sealApi.doc (notes := note v :: shortNote v)
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees)
    contract := Spec.Gcm.sealContract X86_64.abi 2624
    stack := 2624
    verified := sealSel_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkB)
    features := v.features },
  { Spec.Gcm.openApi with
    name := Spec.Gcm.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.openApi.doc (notes := note v :: shortNote v)
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees)
    contract := Spec.Gcm.openContract X86_64.abi 2632
    stack := 2632
    verified := openSel_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkB)
    features := v.features },
  { Spec.Gcm.streamInitApi with
    name := Spec.Gcm.streamInitApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamInitApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit v.callees)
    contract := Spec.Gcm.streamInitContract X86_64.abi 2576
    stack := 2576
    verified := streamInit_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (streamInit_spSafe v)
    features := v.gh.features },
  { Spec.Gcm.streamAadApi with
    name := Spec.Gcm.streamAadApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamAadApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad v.callees)
    contract := Spec.Gcm.streamAadContract X86_64.abi 2576
    stack := 2576
    verified := streamAad_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (streamAad_spSafe v)
    features := v.gh.features },
  { Spec.Gcm.streamEncryptApi with
    name := Spec.Gcm.streamEncryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamEncryptApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.callees)
    contract := Spec.Gcm.streamEncryptContract X86_64.abi 2608
    stack := 2608
    verified := streamEncrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v)
    features := v.features },
  { Spec.Gcm.streamDecryptApi with
    name := Spec.Gcm.streamDecryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamDecryptApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.callees)
    contract := Spec.Gcm.streamDecryptContract X86_64.abi 2608
    stack := 2608
    verified := streamDecrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v)
    features := v.features },
  { Spec.Gcm.streamFinishApi with
    name := Spec.Gcm.streamFinishApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamFinishApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)
    contract := Spec.Gcm.streamFinishContract X86_64.abi 2584
    stack := 2584
    verified := streamFinish_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup },
  { Spec.Gcm.streamVerifyApi with
    name := Spec.Gcm.streamVerifyApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify v.callees)
    contract := Spec.Gcm.streamVerifyContract X86_64.abi 2592
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
  { Spec.Gcm.initPrecomputedApi with
    name := Spec.Gcm.initPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.initPrecomputedApi.doc (notes := [initNoteP v])
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.initPrecomputed v.callees)
    contract := Spec.Gcm.initPrecomputedContract X86_64.abi 2576
    stack := 2576
    verified := initP_framed v
    spSafe := X86_64.withStackScratch_spSafe (by decide) (initP_spSafe v)
    features := (v.ctr.features ++ v.key.features ++ v.gh.features).dedup },
  { Spec.Gcm.encryptBlocksPrecomputedApi with
    name := Spec.Gcm.encryptBlocksPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.encryptBlocksPrecomputedApi.doc (notes := [blocksNoteP v])
    code := v.blkP.enc.code
    contract := Spec.Gcm.encryptBlocksPrecomputedContract X86_64.abi 8
    stack := 8
    verified := encryptBlocksP_verified v v.stitchP
    spSafe := v.blkP.encSp
    features := v.features },
  { Spec.Gcm.decryptBlocksPrecomputedApi with
    name := Spec.Gcm.decryptBlocksPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.decryptBlocksPrecomputedApi.doc (notes := [blocksNoteP v])
    code := v.blkP.dec.code
    contract := Spec.Gcm.decryptBlocksPrecomputedContract X86_64.abi 8
    stack := 8
    verified := decryptBlocksP_verified v v.stitchP
    spSafe := v.blkP.decSp
    features := v.features },
  { Spec.Gcm.sealPrecomputedApi with
    name := Spec.Gcm.sealPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.sealPrecomputedApi.doc (notes := note v :: shortNote v)
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP))
    contract := Spec.Gcm.sealPrecomputedContract X86_64.abi 2624
    stack := 2624
    verified := sealSelP_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkP)
    features := v.features },
  { Spec.Gcm.openPrecomputedApi with
    name := Spec.Gcm.openPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.openPrecomputedApi.doc (notes := note v :: shortNote v)
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk v.blkP))
    contract := Spec.Gcm.openPrecomputedContract X86_64.abi 2632
    stack := 2632
    verified := openSelP_framed v Short.shortFacts
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkP)
    features := v.features },
  { Spec.Gcm.streamEncryptPrecomputedApi with
    name := Spec.Gcm.streamEncryptPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamEncryptPrecomputedApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.withBlk v.blkP))
    contract := Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608
    stack := 2608
    verified := streamEncryptP_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v v.blkP)
    features := v.features },
  { Spec.Gcm.streamDecryptPrecomputedApi with
    name := Spec.Gcm.streamDecryptPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamDecryptPrecomputedApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.withBlk v.blkP))
    contract := Spec.Gcm.streamDecryptPrecomputedContract X86_64.abi 2608
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
  "If the text so far ends a block, this implementation encrypts the whole blocks of the input from \
    `src` to `dst` with `" ++ blk ++ "`; it copies the rest to `dst` and encrypts it there with `" ++
    enc ++ "`."

/-- The instance of `vg_aes_gcm_encrypt_blocks_to` of a variant. -/
def blkTo (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBlocks (Spec.Gcm.encryptBlocksToApi.name ++ v.impl.suffix) v.impl.blkB v.stitchTo

/-- The instance of `vg_aes_gcm_encrypt_blocks_to_precomputed` of a variant. -/
def blkToP (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofBlocks (Spec.Gcm.encryptBlocksToPrecomputedApi.name ++ v.impl.suffix) v.impl.blkP v.stitchToP

/-- The instance of `vg_aes_gcm_stream_encrypt` calling the implementations `v`. -/
def encFn (v : GcmImpl) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.streamEncryptApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.callees)⟩
    (streamEncrypt_framed v) (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v))
    (StreamTo.framed_xdepth (streamEncrypt_xdepth v)) (StreamTo.framed_mx (streamEncrypt_mx v))

/-- The instance of `vg_aes_gcm_stream_encrypt_precomputed` calling the
implementations `v`. -/
def encFnP (v : GcmImpl) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨Spec.Gcm.streamEncryptPrecomputedApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.withBlk v.blkP))⟩
    (streamEncryptP_framed v) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v v.blkP))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v v.blkP)) (StreamTo.framed_mx (streamEncryptM_mx v v.blkP))

/-- `vg_aes_gcm_encrypt_blocks_to` and `vg_aes_gcm_stream_encrypt_to` calling
the implementations `v`, and the `_precomputed` ones if its loops read the
powers from the key context. -/
def artifactsTo (v : GcmVariant) : List Artifact :=
  [{ Spec.Gcm.encryptBlocksToApi with
    name := Spec.Gcm.encryptBlocksToApi.name ++ v.impl.suffix
    target := X86_64.target
    doc := Spec.Gcm.encryptBlocksToApi.doc
      (notes := [blocksToNote v.stitchTo.isSome v.impl.blkB.enc.name])
    code := Impl.AesGcm.X86_64.BlocksTo.encrypt v.impl.blkB.enc (v.stitchTo.map (·.enc))
    contract := Spec.Gcm.encryptBlocksToContract X86_64.abi 24
    stack := 24
    verified := encryptBlocksTo_verified v.impl.blkB v.stitchTo
    spSafe := encryptTo_spSafe v.stitchTo v.impl.blkB
    features := v.impl.features },
  { Spec.Gcm.streamEncryptToApi with
    name := Spec.Gcm.streamEncryptToApi.name ++ v.impl.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamEncryptToApi.doc
      (notes := [streamToNote (blkTo v).fn.name (encFn v.impl).fn.name])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2232 3
      (Impl.AesGcm.X86_64.StreamTo.encrypt (blkTo v).fn (encFn v.impl).fn)
    contract := Spec.Gcm.streamEncryptToContract X86_64.abi 4856
    stack := 4856
    verified := StreamTo.streamEncryptTo_framed (blkTo v) (encFn v.impl)
    spSafe := X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkTo v) (encFn v.impl))
    features := v.impl.features }] ++
  if v.impl.stitchP.isSome then
    [{ Spec.Gcm.encryptBlocksToPrecomputedApi with
      name := Spec.Gcm.encryptBlocksToPrecomputedApi.name ++ v.impl.suffix
      target := X86_64.target
      doc := Spec.Gcm.encryptBlocksToPrecomputedApi.doc
        (notes := [blocksToNote v.stitchToP.isSome v.impl.blkP.enc.name])
      code := Impl.AesGcm.X86_64.BlocksTo.encrypt v.impl.blkP.enc (v.stitchToP.map (·.enc))
      contract := Spec.Gcm.encryptBlocksToPrecomputedContract X86_64.abi 24
      stack := 24
      verified := encryptBlocksToP_verified v.impl.blkP v.stitchToP
      spSafe := encryptTo_spSafe v.stitchToP v.impl.blkP
      features := v.impl.features },
    { Spec.Gcm.streamEncryptToPrecomputedApi with
      name := Spec.Gcm.streamEncryptToPrecomputedApi.name ++ v.impl.suffix
      target := X86_64.target
      doc := Spec.Gcm.streamEncryptToPrecomputedApi.doc
        (notes := [streamToNote (blkToP v).fn.name (encFnP v.impl).fn.name])
      code := Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToP v).fn (encFnP v.impl).fn)
      contract := Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856
      stack := 4856
      verified := StreamTo.streamEncryptToP_framed (blkToP v) (encFnP v.impl)
      spSafe := X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToP v) (encFnP v.impl))
      features := v.impl.features }]
  else []


/-- How an instance of `vg_aes_gcm_seal_gather` works. -/
def gatherNote (enc : String) : String :=
  "This implementation runs the streaming functions on a state of its own: it absorbs the additional \
    data, padded with zeros to a whole block if there is any text (as GHASH pads it), and encrypts \
    each slice from where it is to the output with `" ++ enc ++ "`."

/-- The instance of `vg_aes_gcm_stream_init` calling the implementations `v`. -/
def initFn (v : GcmImpl) : Gather.InitFn :=
  .ofSpec ⟨Spec.Gcm.streamInitApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit v.callees)⟩
    (streamInit_framed v) (X86_64.withStackScratch_spSafe (by decide) (streamInit_spSafe v))
    (Gather.framedS_xdepth (streamInit_xdepth v)) (Gather.framedS_mx (streamInit_mx v))

/-- The instance of `vg_aes_gcm_stream_aad` calling the implementations `v`. -/
def aadFn (v : GcmImpl) : Gather.AadFn :=
  .ofSpec ⟨Spec.Gcm.streamAadApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad v.callees)⟩
    (streamAad_framed v) (X86_64.withStackScratch_spSafe (by decide) (streamAad_spSafe v))
    (Gather.framedS_xdepth (streamAad_xdepth v)) (Gather.framedS_mx (streamAad_mx v))

/-- The instance of `vg_aes_gcm_stream_finish` calling the implementations `v`. -/
def finFn (v : GcmImpl) : Gather.FinFn :=
  .ofSpec ⟨Spec.Gcm.streamFinishApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)⟩
    (streamFinish_framed v) (X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v))
    (StreamTo.framed_xdepth (streamFinish_xdepth v)) (StreamTo.framed_mx (streamFinish_mx v))

/-- The instance of `vg_aes_gcm_stream_encrypt_to` of a variant. -/
def toFn (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.streamEncryptToApi.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkTo v).fn (encFn v.impl).fn)⟩
    (StreamTo.streamEncryptTo_framed (blkTo v) (encFn v.impl))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkTo v) (encFn v.impl)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkTo v) (encFn v.impl)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkTo v) (encFn v.impl)))

/-- The instance of `vg_aes_gcm_stream_encrypt_to_precomputed` of a variant. -/
def toFnP (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨Spec.Gcm.streamEncryptToPrecomputedApi.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToP v).fn (encFnP v.impl).fn)⟩
    (StreamTo.streamEncryptToP_framed (blkToP v) (encFnP v.impl))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToP v) (encFnP v.impl)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToP v) (encFnP v.impl)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToP v) (encFnP v.impl)))

/-- `vg_aes_gcm_seal_gather` calling the implementations `v`, and the
`_precomputed` one if its loops read the powers from the key context. -/
def artifactsGather (v : GcmVariant) : List Artifact :=
  [{ Spec.Gcm.sealGatherApi with
    name := Spec.Gcm.sealGatherApi.name ++ v.impl.suffix
    target := X86_64.target
    doc := Spec.Gcm.sealGatherApi.doc (notes := [gatherNote (toFn v).fn.name])
    code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn
        (finFn v.impl).fn)
    contract := Spec.Gcm.sealGatherContract X86_64.abi 5128
    stack := 5128
    verified := Gather.sealGather_framed (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)
    spSafe := X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))
    features := v.impl.features }] ++
  if v.impl.stitchP.isSome then
    [{ Spec.Gcm.sealGatherPrecomputedApi with
      name := Spec.Gcm.sealGatherPrecomputedApi.name ++ v.impl.suffix
      target := X86_64.target
      doc := Spec.Gcm.sealGatherPrecomputedApi.doc (notes := [gatherNote (toFnP v).fn.name])
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (initFn v.impl).fn (aadFn v.impl).fn (toFnP v).fn
          (finFn v.impl).fn)
      contract := Spec.Gcm.sealGatherPrecomputedContract X86_64.abi 5128
      stack := 5128
      verified := Gather.sealGatherP_framed (initFn v.impl) (aadFn v.impl) (toFnP v) (finFn v.impl)
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (initFn v.impl) (aadFn v.impl) (toFnP v) (finFn v.impl))
      features := v.impl.features }]
  else []

/-- The artifacts of a variant, from the implementations it names: the
`_precomputed` ones too if its loops read the powers from the key context. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ (if v.impl.stitchP.isSome then artifactsP v.impl else []) ++ artifactsTo v ++
    artifactsGather v

end VG.Generic.AesGcm.X86_64.AesGcm
