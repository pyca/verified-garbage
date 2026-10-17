module

public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKeyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-384 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-384's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-384's
verified compression function.

`finalize` finalizes the inner state with SHA-384's verified streaming
`finalize`, then computes the outer hash as one call of SHA-512's verified
compression function (`vg_sha512_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` takes a key of any length (`initAnyKeyApi`): a key longer than a block
is first hashed with SHA-384's verified streaming functions into its working
space, as PBKDF2's `pbkdf2` hashes a long password
(`Impl/Pbkdf2/Md/AnyKey/Arm.lean`), and `init_scratch`, the code above with
its working space as an argument, is called with the key or its digest.
`init` keeps its working space in a frame of its own, which it wipes before
returning (`Proof/Pbkdf2/Whole/Arm/AnyKeyCT.lean`); `finalize` keeps its in a
frame of its own too (`Proof/Pbkdf2/Md/Arm/Frame.lean`). `init_scratch` and
`finalize_scratch` are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha384.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped (Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha384I) 0
      (2 * Spec.Hmac.sha384I.initAnyKeyScratch) Proof.Pbkdf2.Whole.Arm.sha384F.hmacInitAny
    stack := 24 + Proof.Pbkdf2.Whole.Arm.Any.anyFrame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Whole.Arm.Any.sha384_anyFramed },
  Spec.Hmac.sha384I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I) 1 Proof.Pbkdf2.Md.Arm.sha384Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha384I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha384_finalize
      Proof.Hmac.sha384_local Proof.Pbkdf2.Md.Arm.sha384_finFrameSat },
  Spec.Hmac.sha384I.initScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha384Md.hmacInit
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha384_init },
  Spec.Hmac.sha384I.finalizeScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha384Md.hmacFin
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha384_finalize }]

end VG.Artifacts.HmacSha384.Arm
