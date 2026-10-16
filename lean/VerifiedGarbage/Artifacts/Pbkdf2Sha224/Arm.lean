module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# PBKDF2-HMAC-SHA-224 (RFC 8018) on ARMv7: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`): each step is two calls of SHA-256's verified
compression function (`vg_sha256_compress`), on blocks laid out once at fixed
offsets in `scratch`. It uses no stack; `stack` is that of the shared
contract, 16 bytes.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/Arm.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above. `stack` is
that of the shared contract, 24 bytes: `pbkdf2` pushes `update`'s 16 bytes of
stack arguments, or 8 bytes around a call of a function that uses 16. It
runs in a frame holding its working space
(`Proof.Pbkdf2.Whole.Arm.pbkFramed`).
-/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha224.Arm

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.iterateApi.artifact Arm.target {
    code := Proof.Pbkdf2.Md.Arm.sha224Md.iterate
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_iterate },
  Spec.Hmac.sha224I.pbkdf2Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha224I) 3
      Proof.Pbkdf2.Whole.Arm.sha224F.pbkdf2
    stack := 24 + Proof.Pbkdf2.Whole.Arm.pbkFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Whole.Arm.pbkFramed Proof.Pbkdf2.Whole.Arm.sha224
      Proof.Pbkdf2.Whole.Arm.sha224_pbkFrameSat }]

end VG.Artifacts.Pbkdf2Sha224.Arm
