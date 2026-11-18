module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sha512.Scratch
public import VerifiedGarbage.Proof.Sha512.Digest
public import VerifiedGarbage.Proof.MdStream.DigestScratch
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on PPC64LE, without secret residue

The streaming functions with frames and the one-shot digests, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Sha512/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha512_update`. -/
def updateReg : Registration Spec.Sha512.updateApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r7 Impl.Sha512.PPC64LE.Stream.update
      verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePostOut_local 64))

/-- `vg_sha512_finalize`. -/
def finalizeReg : Registration Spec.Sha512.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePostOut_local 64))

/-- `vg_sha384_finalize`. -/
def finalize384Reg : Registration Spec.Sha512.finalize384Api PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize384
      verified := Shared.finalize384 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPostOut_local Spec.Sha512.H0_384 48 Spec.Sha512.sha384 64))

/-- `vg_sha512_224_finalize`. -/
def finalize512_224Reg : Registration Spec.Sha512.finalize512_224Api PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_224
      verified := Shared.finalize512_224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPostOut_local Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 64))

/-- `vg_sha512_256_finalize`. -/
def finalize512_256Reg : Registration Spec.Sha512.finalize512_256Api PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_256
      verified := Shared.finalize512_256 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPostOut_local Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 64))

/-- `vg_sha384_digest`. -/
def digest384Reg : Registration Spec.Sha512.digest384Api PPC64LE.target :=
  withScrub {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha384.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha384.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 48 Spec.Sha512.sha384 64))

/-- `vg_sha512_digest`. -/
def digest512Reg : Registration Spec.Sha512.digest512Api PPC64LE.target :=
  withScrub {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha512.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha512.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 64 Spec.Sha512.sha512 64))

/-- `vg_sha512_224_digest`. -/
def digest512_224Reg : Registration Spec.Sha512.digest512_224Api PPC64LE.target :=
  withScrub {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha512_224.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 28 Spec.Sha512.sha512_224 64))

/-- `vg_sha512_256_digest`. -/
def digest512_256Reg : Registration Spec.Sha512.digest512_256Api PPC64LE.target :=
  withScrub {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha512_256.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha512_256.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 32 Spec.Sha512.sha512_256 64))

/-- Each of them is scrubbed: `withScrub`'s side conditions hold. -/
example : updateReg.residue.isSome ∧
    finalizeReg.residue.isSome ∧
    finalize384Reg.residue.isSome ∧
    finalize512_224Reg.residue.isSome ∧
    finalize512_256Reg.residue.isSome ∧
    digest384Reg.residue.isSome ∧
    digest512Reg.residue.isSome ∧
    digest512_224Reg.residue.isSome ∧
    digest512_256Reg.residue.isSome := by
  decide

end VG.Proof.Sha512.PPC64LE
