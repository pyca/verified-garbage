module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Verified
public import VerifiedGarbage.Proof.GcmSiv.Polyval
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
frame. The proofs take the tag input computed with GHASH to be RFC 8452's
(`TagInputEq`), bound here to `Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`,
so that only this file imports the algebra of its proof.
-/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.PPC64LE

open VG.Proof.AesGcmSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 Impl.AesGcmSiv.PPC64LE.«seal»
    stack := 3936
    verified := seal_framed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG },
  Spec.GcmSiv.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 Impl.AesGcmSiv.PPC64LE.«open»
    stack := 3936
    verified := open_framed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG }]

end VG.Artifacts.AesGcmSiv.PPC64LE
