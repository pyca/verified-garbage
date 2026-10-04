import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# AES-GCM-SIV (RFC 8452) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), are emitted once for each combination
(`Variants/AesGcm/X86_64/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aesni_pclmul`), and need the CPU features of the three.
They do not call AES-GCM's interleaved loops, so the instances of
combinations differing only in those are the same code under other names,
which keeps every instance of a combination callable together.

The stack is 8 bytes for each: the return address of a call of one of the
three, which make no calls; `seal` and `open` also read their seventh
argument, the working space's address, from the stack above their return
address.
-/

namespace VG.Generic.AesGcm.X86_64.AesGcmSiv

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and computes POLYVAL with `" ++ v.gh.fn.name ++ "`."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  { Spec.GcmSiv.sealApi with
    name := Spec.GcmSiv.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.GcmSiv.sealApi.doc (notes := [note v])
    code := Impl.AesGcmSiv.X86_64.«seal» v.callees
    contract := Spec.GcmSiv.sealContract X86_64.abi 8
    stack := 8
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := features v },
  { Spec.GcmSiv.openApi with
    name := Spec.GcmSiv.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesGcmSiv.X86_64.«open» v.callees
    contract := Spec.GcmSiv.openContract X86_64.abi 8
    stack := 8
    verified := open_verified v
    spSafe := open_spSafe v
    features := features v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86_64.AesGcmSiv
