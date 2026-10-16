module

public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC-SHA-256 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-256's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-256's
verified compression function.

`finalize` finalizes the inner state with SHA-256's verified streaming
`finalize`, then computes the outer hash as one call of SHA-256's verified
compression function (`vg_sha256_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.

`init` and `finalize` keep their working space in a frame of their own
(`Proof/Pbkdf2/Md/Arm/Frame.lean`); `init_scratch` and `finalize_scratch`, the
same code with it as an argument, are what PBKDF2's code calls.
-/

@[expose] public section

namespace VG.Artifacts.HmacSha256.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 0 Proof.Pbkdf2.Md.Arm.sha256Md.hmacInit
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.Arm.initFramed Proof.Pbkdf2.Md.Arm.Instances.sha256_init
      Proof.Pbkdf2.Md.Arm.sha256_initFrameSat },
  Spec.Hmac.sha256I.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1 Proof.Pbkdf2.Md.Arm.sha256Md.hmacFin
    stack := 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha256_finalize
      Proof.Hmac.sha256_local Proof.Pbkdf2.Md.Arm.sha256_finFrameSat },
  Spec.Hmac.sha256I.initScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha256Md.hmacInit
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha256_init },
  Spec.Hmac.sha256I.finalizeScratchApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha256Md.hmacFin
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha256_finalize }]

end VG.Artifacts.HmacSha256.Arm
