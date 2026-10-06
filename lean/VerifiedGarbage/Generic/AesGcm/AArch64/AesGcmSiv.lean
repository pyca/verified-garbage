import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls

/-!
# AES-GCM-SIV (RFC 8452) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), are emitted once for each combination
(`Variants/AesGcm/AArch64/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aes`), and need the CPU features of the three.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; these artifacts are made from each function's `Api` (in
`Spec/`, reviewed with the contract), and this file adds only notes on the
implementation.

Each keeps its working space in a frame of 3824 bytes on the stack
(`Proof/AesGcmSiv/AArch64/Verified.lean`); their calls (`bl`) keep the return
address in `x30`, which they save in the working space, with our caller's
registers, so no other stack is used.
-/

namespace VG.Generic.AesGcm.AArch64.AesGcmSiv

open VG.Proof.AesGcm.AArch64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.AArch64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and computes POLYVAL with `" ++ v.gh.fn.name ++ "`."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  { Spec.GcmSiv.sealApi with
    name := Spec.GcmSiv.sealApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.GcmSiv.sealApi.doc (notes := [note v])
    code := Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Impl.AesGcmSiv.AArch64.«seal» v.callees)
    contract := Spec.GcmSiv.sealContract AArch64.abi 3824
    stack := 3824
    verified := seal_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.GcmSiv.openApi with
    name := Spec.GcmSiv.openApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Impl.AesGcmSiv.AArch64.«open» v.callees)
    contract := Spec.GcmSiv.openContract AArch64.abi 3824
    stack := 3824
    verified := open_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.AArch64.AesGcmSiv
