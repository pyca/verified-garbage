module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeySha256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-224 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-224's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-256's
verified compression function (`vg_sha256_compress`).

`finalize` finalizes the inner state with SHA-256's verified streaming
`finalize`, then computes the outer hash as one call of SHA-256's verified
compression function (`vg_sha256_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` takes a key of any length (`initAnyKeyApi`), and chooses on entry by
its public length (`Proof/Pbkdf2/Whole/Arm/AnyKeyEntry.lean`): a key of at
most a block goes straight to `init_scratch`, the code above with its working
space as an argument, in a frame of its own holding its working space
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); a longer key is first hashed with
SHA-224's verified streaming functions into its working space, as
PBKDF2's `pbkdf2` hashes a long password (`Impl/Pbkdf2/Md/AnyKey/Arm.lean`),
and `init_scratch` is called with its digest, in a larger frame of its own,
which it wipes before returning (`Proof/Pbkdf2/Whole/Arm/AnyKeyCT.lean`);
`stack` is that of the larger. `finalize` keeps its working space in a frame
of its own too (`Proof/Pbkdf2/Md/Arm/Frame.lean`). `init_scratch` and
`finalize_scratch` are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact Arm.target {
    code := Proof.Pbkdf2.Whole.Arm.initCode Spec.Hmac.sha224I Proof.Pbkdf2.Md.Arm.sha224Md.hmacInit Proof.Pbkdf2.Whole.Arm.sha224F
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha224_initF },
  Spec.Hmac.sha224I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I) 1 Proof.Pbkdf2.Md.Arm.sha224Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize
      Proof.Hmac.sha224_local Proof.Pbkdf2.Md.Arm.sha224_finFrameSat },
  Spec.Hmac.sha224I.initScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha224Md.hmacInit
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_init },
  Spec.Hmac.sha224I.finalizeScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha224Md.hmacFin
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize }]

end VG.Artifacts.HmacSha224.Arm
