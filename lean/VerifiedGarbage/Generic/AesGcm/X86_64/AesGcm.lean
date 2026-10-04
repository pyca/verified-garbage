import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# AES-GCM (NIST SP 800-38D) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash`,
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
it (`GcmImpl.stitch`).

The stack is 8 bytes for `stream_finish` and `stream_verify`: the return
address of a call of `vg_aes_expand_key`, `vg_aes_ctr32` or `vg_ghash`, which
make no calls. `init`, `stream_init` and `stream_aad` need 2568 bytes more,
for the frame that holds their working space.
`seal`, `open`, `stream_encrypt` and `stream_decrypt` need 24: the argument
they pass on the stack, the return address of their call of
`vg_aes_gcm_encrypt_blocks` or `vg_aes_gcm_decrypt_blocks`, and that of its
calls. `stream_encrypt` and `stream_decrypt` need 2584 bytes more, for the
frame that holds their working space, which was their second stack argument
(`Verified.stackArgScratch`).
-/

namespace VG.Generic.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and hashes with `" ++ v.gh.fn.name ++ "`."

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
    spSafe := encryptBlocks_spSafe v v.stitch
    features := v.features },
  { Spec.Gcm.decryptBlocksApi with
    name := Spec.Gcm.decryptBlocksApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.decryptBlocksApi.doc (notes := [blocksNote v])
    code := v.callees.dec.code
    contract := Spec.Gcm.decryptBlocksContract X86_64.abi 8
    stack := 8
    verified := decryptBlocks_verified v v.stitch
    spSafe := decryptBlocks_spSafe v v.stitch
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
    doc := Spec.Gcm.sealApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.«seal» v.callees
    contract := Spec.Gcm.sealContract X86_64.abi 24
    stack := 24
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.Gcm.openApi with
    name := Spec.Gcm.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.openApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.«open» v.callees
    contract := Spec.Gcm.openContract X86_64.abi 24
    stack := 24
    verified := open_verified v
    spSafe := open_spSafe v
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
    code := Impl.AesGcm.X86_64.streamFinish v.callees
    contract := Spec.Gcm.streamFinishContract X86_64.abi 8
    stack := 8
    verified := streamFinish_verified v
    spSafe := streamFinish_spSafe v
    features := (v.ctr.features ++ v.gh.features).dedup },
  { Spec.Gcm.streamVerifyApi with
    name := Spec.Gcm.streamVerifyApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamVerify v.callees
    contract := Spec.Gcm.streamVerifyContract X86_64.abi 8
    stack := 8
    verified := streamVerify_verified v
    spSafe := streamVerify_spSafe v
    features := (v.ctr.features ++ v.gh.features).dedup }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86_64.AesGcm
