import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls

/-!
# AES-GCM-SIV (RFC 8452) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), and the implementation of `vg_aes_encrypt_blocks` that
goes with `v`'s `vg_aes_ctr32` (`ecbOf`), are emitted once for each combination
(`Variants/AesGcm/X86_64/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aesni_pclmul`), and need the CPU features of the four.
They do not call AES-GCM's interleaved loops, so the instances of
combinations differing only in those are the same code under other names,
which keeps every instance of a combination callable together.

Each keeps its working space in a frame of 3848 bytes on the stack
(`Proof/AesGcmSiv/X86_64/Verified.lean`), below which its calls use 8 bytes:
the return address of a call of one of the four, which make no calls.
-/

namespace VG.Generic.AesGcm.X86_64.AesGcmSiv

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ (ecbOf v).enc.name ++ "` and `" ++ v.ctr.callee.name ++
    "` (and expands keys with `" ++ v.key.fn.name ++ "`) and computes POLYVAL with `" ++ v.gh.fn.name ++ "`."

/-- The implementation of `vg_aes_encrypt_blocks` they call. -/
def ecbFn (v : GcmImpl) : Impl.AesGcm.X86_64.Fn := ⟨(ecbOf v).enc.name, (ecbOf v).enc.code⟩

/-- The artifacts calling the implementations `v`, named with `sfx` after its
suffix. -/
def artifactsOf (v : GcmImpl) (sfx : String) : List Artifact := [
  { Spec.GcmSiv.sealApi with
    name := Spec.GcmSiv.sealApi.name ++ v.suffix ++ sfx
    target := X86_64.target
    doc := Spec.GcmSiv.sealApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (Impl.AesGcmSiv.X86_64.«seal» v.callees (ecbFn v))
    contract := Spec.GcmSiv.sealContract X86_64.abi 3856
    stack := 3856
    verified := seal_framed v (ecbOf v)
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v (ecbOf v))
    features := features v },
  { Spec.GcmSiv.openApi with
    name := Spec.GcmSiv.openApi.name ++ v.suffix ++ sfx
    target := X86_64.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (Impl.AesGcmSiv.X86_64.«open» v.callees (ecbFn v))
    contract := Spec.GcmSiv.openContract X86_64.abi 3856
    stack := 3856
    verified := open_framed v (ecbOf v)
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v (ecbOf v))
    features := features v }]

/-- The artifacts of a variant, from the implementations it names: its
`vg_aes_ctr32`, key expansion and `vg_ghash`, without its interleaved loops,
which these do not call (so this file need not import their proofs, from
`Generic/AesGcm/X86_64/AesGcm.lean`), named as AES-GCM's instances of the
variant are (`GcmImpl.suffix`: the callees' suffixes, then the loops'). -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf ⟨v.ctr, v.key, v.gh.impl, none, none, false⟩ ((v.stitch.map (·.suffix)).getD "")

end VG.Generic.AesGcm.X86_64.AesGcmSiv
