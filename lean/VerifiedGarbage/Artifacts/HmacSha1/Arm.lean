module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-1 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with SHA-1's
verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word by word
into their buffers, and absorbs each with one call of SHA-1's verified
compression function.

`finalize` finalizes the inner state with SHA-1's verified streaming
`finalize`, then computes the outer hash as one call of SHA-1's verified
compression function (`vg_sha1_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` takes a key of any length (`initAnyKeyApi`), and chooses on entry by
its public length (`Proof/Pbkdf2/Whole/Arm/AnyKeyEntry.lean`): a key of at
most a block goes straight to `init_scratch`, the code above with its working
space as an argument, in a frame of its own holding its working space
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); a longer key is first hashed with
SHA-1's verified streaming functions into its working space, as
PBKDF2's `pbkdf2` hashes a long password (`Impl/Pbkdf2/Md/AnyKey/Arm.lean`),
and `init_scratch` is called with its digest, in a larger frame of its own,
which it wipes before returning (`Proof/Pbkdf2/Whole/Arm/AnyKeyCT.lean`);
`stack` is that of the larger. `finalize` keeps its working space in a frame
of its own too (`Proof/Pbkdf2/Md/Arm/Frame.lean`). `init_scratch` and
`finalize_scratch` are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha1.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha1I Proof.Pbkdf2.Md.Arm.sha1Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha1F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha1_initF },
  Spec.Hmac.sha1I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I) 1 Proof.Pbkdf2.Md.Arm.sha1Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha1I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha1_finalize
      Proof.Hmac.sha1_local Proof.Pbkdf2.Md.Arm.sha1_finFrameSat },
  Spec.Hmac.sha1I.initScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha1Md.hmacInit
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha1_init },
  Spec.Hmac.sha1I.finalizeScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha1Md.hmacFin
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha1_finalize }]

end VG.Artifacts.HmacSha1.Arm
