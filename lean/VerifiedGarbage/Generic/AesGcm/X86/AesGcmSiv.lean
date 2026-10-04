import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcmSiv.X86.Verified
import VerifiedGarbage.Generic.AesGcm.X86.AesGcm

/-!
# AES-GCM-SIV (RFC 8452) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), are emitted once for each combination
(`Variants/AesGcm/X86/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aesni_pclmul`), and need the CPU features of the three.

The stack is 28 bytes for each: a call of `vg_aes_ctr32` (six arguments and
the return address; the calls of the other two push fewer), which makes no
calls. Both functions keep their arguments, and our caller's registers, in
`work`.
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
    code := Impl.AesGcmSiv.X86.«seal» v.callees
    contract := Spec.GcmSiv.sealContract X86.abi 28
    stack := 28
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.GcmSiv.openApi with
    name := Spec.GcmSiv.openApi.name ++ v.suffix
    target := X86.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesGcmSiv.X86.«open» v.callees
    contract := Spec.GcmSiv.openContract X86.abi 28
    stack := 28
    verified := open_verified v
    spSafe := open_spSafe v
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86.AesGcmSiv
