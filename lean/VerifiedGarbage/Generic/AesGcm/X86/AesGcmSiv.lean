import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcmSiv.X86.Frame
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Generic.AesGcm.X86.AesGcm

/-!
# AES-GCM-SIV (RFC 8452) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), are emitted once for each combination
(`Variants/AesGcm/X86/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aesni_pclmul`), and need the CPU features of the three.

Each runs in a frame of 2856 bytes holding its working space and a copy of
its eight stack arguments (`Proof/AesGcmSiv/X86/Frame.lean`), below which it
uses 28 bytes: a call of `vg_aes_ctr32` (six arguments and the return
address; the calls of the other two push fewer), which makes no calls;
2884 bytes in all. The proofs take the tag input computed with GHASH to be
RFC 8452's (`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`), which this file
imports, with its algebra, so that the proofs need not.
-/

namespace VG.Generic.AesGcm.X86.AesGcmSiv

open VG.Proof.AesGcm.X86 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.ctr.expand.name ++ "`) and computes POLYVAL with `" ++ v.gh.fn.name ++ "`."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  { Spec.GcmSiv.sealApi with
    name := Spec.GcmSiv.sealApi.name ++ v.suffix
    target := X86.target
    doc := Spec.GcmSiv.sealApi.doc (notes := [note v])
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«seal» v.callees)
    contract := Spec.GcmSiv.sealContract X86.abi 2884
    stack := 2884
    verified := seal_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (by decide) (seal_spSafe v)
    features := v.features },
  { Spec.GcmSiv.openApi with
    name := Spec.GcmSiv.openApi.name ++ v.suffix
    target := X86.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«open» v.callees)
    contract := Spec.GcmSiv.openContract X86.abi 2884
    stack := 2884
    verified := open_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (by decide) (open_spSafe v)
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86.AesGcmSiv
