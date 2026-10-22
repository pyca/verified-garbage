module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# SM4-GCM (NIST SP 800-38D, RFC 8998) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementation `n` of `vg_ghash`, are emitted once for each
(`Variants/Ghash/X86_64/`), named with its suffix (e.g.
`vg_sm4_gcm_seal_pclmul`), and need its CPU features; they encrypt with
`vg_sm4_ctr32`, in the baseline ISA. `vg_sm4_gcm_init`, which does not hash,
is registered once (`Artifacts/Sm4Gcm/X86_64.lean`). `stream_init` and
`stream_aad`, which only hash, are AES-GCM's code (and proofs), whose
contracts theirs are. **Review note**: `sig` and `doc` are trusted, as they
tie the Rust caller to the contract; these artifacts are made from each
function's `Api` (in `Spec/`, reviewed with the contract), and this file adds
only notes on the implementation.

Every function keeps its working space in a frame on the stack
(`Proof/Sm4Gcm/X86_64/Frame.lean`): 2568 bytes for `stream_init`,
`stream_aad` and `stream_finish` (`Verified.stackScratch`), and for the
others, whose working space is their last argument passed on the stack, a
frame that also holds a copy of their other stack arguments
(`Verified.stackArgScratch`): 2576 bytes for `stream_encrypt`,
`stream_decrypt` and `stream_verify`, 2592 for `seal` and 2600 for `open`.
Below it, `stream_init` and `stream_aad` use 8 bytes, the return address of
their calls of `vg_ghash`, which makes none; the others 3224, those of their
calls of `vg_sm4_ctr32`, whose frame takes 3208.
-/

@[expose] public section

namespace VG.Generic.Ghash.X86_64.Sm4Gcm

open VG.Proof.AesGcm.X86_64 (GhashName)
open VG.Proof.Sm4Gcm.X86_64

/-- Which implementations an instance calls. -/
def note (n : GhashName) : String :=
  "This implementation encrypts with `vg_sm4_ctr32` and hashes with `" ++ n.impl.fn.name ++ "`."

/-- Which implementation an instance that only hashes calls. -/
def hashNote (n : GhashName) : String :=
  "This implementation hashes with `" ++ n.impl.fn.name ++ "`."

/-- The artifacts calling the implementation `n` of `vg_ghash`. -/
def artifacts (n : GhashName) : List Artifact := [
  Spec.Sm4.Gcm.sealApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [note n, "It encrypts the data and then hashes the ciphertext, in two passes."]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2592 2 (Impl.Sm4Gcm.X86_64.«seal» (gcmOf n).callees)
    stack := 5816
    verified := seal_framed (gcmOf n)
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.openApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [note n, "It hashes the ciphertext and compares the tags without a branch on the bytes, \
      then decrypts the data only if they are equal."]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (Impl.Sm4Gcm.X86_64.«open» (gcmOf n).callees)
    stack := 5824
    verified := open_framed (gcmOf n)
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.streamInitApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [hashNote n, "It is `vg_aes_gcm_stream_init`'s code, which reads only the hash subkey \
      of the key context."]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit (gcmOf n).callees)
    stack := 2576
    verified := Proof.AesGcm.X86_64.streamInit_framed (gcmOf n)
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.AesGcm.X86_64.streamInit_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.streamAadApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [hashNote n, "It is `vg_aes_gcm_stream_aad`'s code, which reads only the hash subkey \
      of the key context."]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad (gcmOf n).callees)
    stack := 2576
    verified := Proof.AesGcm.X86_64.streamAad_framed (gcmOf n)
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.AesGcm.X86_64.streamAad_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.streamEncryptApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [note n]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0
      (Impl.Sm4Gcm.X86_64.streamEncrypt (gcmOf n).callees)
    stack := 5800
    verified := streamEncrypt_framed (gcmOf n)
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.streamDecryptApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [note n]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0
      (Impl.Sm4Gcm.X86_64.streamDecrypt (gcmOf n).callees)
    stack := 5800
    verified := streamDecrypt_framed (gcmOf n)
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.streamFinishApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [note n]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.Sm4Gcm.X86_64.streamFinish (gcmOf n).callees)
    stack := 5792
    verified := streamFinish_framed (gcmOf n)
    spSafe := X86_64.withStackScratch_spSafe_of (streamFinish_spSafe (gcmOf n))
    features := n.impl.features },
  Spec.Sm4.Gcm.streamVerifyApi.artifact X86_64.target {
    suffix := n.impl.suffix
    notes := [note n, "It compares the tags without a branch on their bytes."]
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0
      (Impl.Sm4Gcm.X86_64.streamVerify (gcmOf n).callees)
    stack := 5800
    verified := streamVerify_framed (gcmOf n)
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (gcmOf n))
    features := n.impl.features }]

end VG.Generic.Ghash.X86_64.Sm4Gcm
