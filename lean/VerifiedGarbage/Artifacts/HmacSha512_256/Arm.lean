module

public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-512/256 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-512/256's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad`
word by word into their buffers, and absorbs each with one call of
SHA-512/256's verified compression function.

`finalize` finalizes the inner state with SHA-512/256's verified streaming
`finalize`, then computes the outer hash as one call of SHA-512's verified
compression function (`vg_sha512_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 0 Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacInit
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Md.Arm.initFramed Proof.Pbkdf2.Md.Arm.Instances.sha512_256_init
      Proof.Pbkdf2.Md.Arm.sha512_256_initFrameSat },
  Spec.Hmac.sha512_256I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I) 1 Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha512_256I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finalize
      Proof.Hmac.sha512_256_local Proof.Pbkdf2.Md.Arm.sha512_256_finFrameSat },
  Spec.Hmac.sha512_256I.initScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacInit
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha512_256_init },
  Spec.Hmac.sha512_256I.finalizeScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacFin
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finalize }]

end VG.Artifacts.HmacSha512_256.Arm
