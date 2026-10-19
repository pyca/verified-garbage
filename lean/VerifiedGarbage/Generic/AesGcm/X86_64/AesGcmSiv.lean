module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

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

`open` deciphers and computes POLYVAL in one interleaved loop
(`Impl.AesGcmSiv.X86_64Stitch`) from 256 bytes of data on with
the implementations whose `vg_aes_ctr32` uses VAES and whose `vg_ghash` uses
VPCLMULQDQ (`sivStitch`), whose CPU features that loop needs; with them,
`seal` computes POLYVAL and enciphers the data's 256-byte groups in loops of
its own.

Each keeps its working space in a frame of 3848 bytes on the stack
(`Proof/AesGcmSiv/X86_64/Verified.lean`), below which its calls use 8 bytes:
the return address of a call of one of the four, which make no calls.
-/

@[expose] public section

namespace VG.Generic.AesGcm.X86_64.AesGcmSiv

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ (ecbOf v).enc.name ++ "` and `" ++ v.ctr.callee.name ++
    "` (and expands keys with `" ++ v.key.fn.name ++ "`) and computes POLYVAL with `" ++ v.gh.fn.name ++ "`."

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v]
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v)
    stack := 3856
    verified := sealCode_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v)
    features := features v },
  Spec.GcmSiv.openApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v)
    stack := 3856
    verified := openCode_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v)
    features := features v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86_64.AesGcmSiv
