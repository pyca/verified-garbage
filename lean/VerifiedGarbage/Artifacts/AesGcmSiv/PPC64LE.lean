module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM-SIV (RFC 8452) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. PPC64LE has one implementation of `vg_aes_ctr32`,
`vg_aes_expand_key_scratch` and `vg_ghash`, so these are not generic over
them.

Both functions run in a frame of 3936 bytes holding their working space
(`Proof/AesGcmSiv/PPC64LE/Verified.lean`). A call (`bl`) stores nothing in
memory, and the functions they call use no stack: their `stack` is that
frame.
-/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.PPC64LE

open VG.Proof.AesGcmSiv.PPC64LE

/-- Which functions the implementation calls. -/
def note : String := "This implementation encrypts with `vg_aes_ctr32` (and expands keys with \
  `vg_aes_expand_key_scratch`) and computes POLYVAL with `vg_ghash`."

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 Impl.AesGcmSiv.PPC64LE.«seal»
    stack := 3936
    verified := seal_framed },
  Spec.GcmSiv.openApi.artifact PPC64LE.target {
    notes := [note,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 Impl.AesGcmSiv.PPC64LE.«open»
    stack := 3936
    verified := open_framed }]

end VG.Artifacts.AesGcmSiv.PPC64LE
