import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.OkP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Ok

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

On x86-64 the key context is that of `vg_aes_gcm_init_precomputed`
(`Spec/Gcm/Precomputed.lean`): `vg_aes_gcm_init`'s, with the powers
`H¹ … H⁴⁸` of the hash subkey after it, which `init_precomputed` computes once
with `vg_ghash` (`InitP.lean`). `seal`, `open`, `stream_encrypt` and
`stream_decrypt` are their `_precomputed` versions, and the interleaved loops
that need the powers read them from it (`GcmImpl.stitchP`) instead of
computing them on every call; `stream_init`, `stream_aad`, `stream_finish` and
`stream_verify` read its first 256 bytes, `vg_aes_gcm_init`'s key context.

Each function needs the CPU features of the implementations it calls:
`init_precomputed` calls AES's and GHASH's, `stream_init` and `stream_aad`
only GHASH's (so their `_aesni` instances are the baseline code under another
name, which keeps every instance of a combination callable together), and
`stream_finish` and `stream_verify` only both's (they do not call the
interleaved loops, whose features `GcmImpl.features` adds).

`seal_precomputed`, `open_precomputed`, `stream_encrypt_precomputed` and
`stream_decrypt_precomputed` encrypt or decrypt and absorb the whole blocks of
the data in one call of the instance of
`vg_aes_gcm_encrypt_blocks_precomputed` or `_decrypt_blocks_precomputed` for
the same combination, which interleaves the two for the implementations that
allow it.

The code of `init_precomputed`, `stream_init`, `stream_aad`, `stream_finish`
and `stream_verify` uses 8 bytes of stack: the return address of a call of
`vg_aes_expand_key_scratch`, `vg_aes_ctr32` or `vg_ghash`, which make no
calls. That of `seal_precomputed`, `open_precomputed`,
`stream_encrypt_precomputed` and `stream_decrypt_precomputed` uses 24: the
argument they pass on the stack, the return address of their call of the
whole-blocks function, and that of its calls. Every function keeps its
working space in a frame on the stack: 2568 bytes for `init_precomputed`,
`stream_init` and `stream_aad` (`Verified.stackScratch`), and for the others,
whose working space is their last argument passed on the stack, a frame that
also holds a copy of their other stack arguments
(`Verified.stackArgScratch`): 2576 bytes for `stream_finish`, 2584 for
`stream_verify`, `stream_encrypt_precomputed` and
`stream_decrypt_precomputed`, 2600 for `seal_precomputed` and 2608 for
`open_precomputed`.
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

/-- The loops named `n` for a key context of `vg_aes_gcm_init_precomputed`
interleave counter mode and GHASH correctly. -/
theorem StitchName.okP : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP n.decP
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok.toM _
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZP.stitchP_ok.toM
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx.stitch_ok.toM _

/-- The loops `p` names, with their proof. -/
def StitchPart.impl (p : StitchPart) : StitchImpl :=
  ⟨p.suffix, p.features, p.name.enc, p.name.dec, p.name.ok, p.encP, p.decP⟩

/-- The loops `p` names for a key context of `vg_aes_gcm_init_precomputed`,
with their proof. -/
def StitchPart.implP (p : StitchPart) : StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  ⟨p.name.encP, p.name.decP, p.name.okP, p.encPP, p.decPP⟩

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl :=
  ⟨v.ctr, v.key, v.gh.impl, v.stitch.map StitchPart.impl, v.stitch.map StitchPart.implP⟩

end VG.Proof.AesGcm.X86_64

namespace VG.Generic.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and hashes with `" ++ v.gh.fn.name ++ "`."

/-- How an instance of `vg_aes_gcm_encrypt_blocks_precomputed` or
`_decrypt_blocks_precomputed` works. -/
def blocksNoteP (v : GcmImpl) : String :=
  if v.stitchP.isSome then
    "This implementation interleaves the AES rounds of 16 blocks at a time with GHASH's \
      multiplications of the 16 blocks before them, from the powers of the hash subkey it \
      reads from the key context, and handles the rest with `" ++ v.ctr.callee.name ++ "` and `" ++
      v.gh.fn.name ++ "`."
  else
    "This implementation calls `" ++ v.ctr.callee.name ++ "` and `" ++ v.gh.fn.name ++ "`."

/-- How an instance of `vg_aes_gcm_init_precomputed` works. -/
def initNoteP (v : GcmImpl) : String :=
  note v ++ " It computes the powers of the hash subkey with `" ++ v.gh.fn.name ++ "`, one at a time."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
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
    features := (v.ctr.features ++ v.gh.features).dedup },
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
    doc := Spec.Gcm.sealPrecomputedApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.«seal» (v.withBlk v.blkP))
    contract := Spec.Gcm.sealPrecomputedContract X86_64.abi 2624
    stack := 2624
    verified := sealP_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (sealM_spSafe v v.blkP)
    features := v.features },
  { Spec.Gcm.openPrecomputedApi with
    name := Spec.Gcm.openPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.openPrecomputedApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.«open» (v.withBlk v.blkP))
    contract := Spec.Gcm.openPrecomputedContract X86_64.abi 2632
    stack := 2632
    verified := openP_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (openM_spSafe v v.blkP)
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

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86_64.AesGcm
