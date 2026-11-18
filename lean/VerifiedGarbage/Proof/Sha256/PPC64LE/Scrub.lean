module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Sha256.PostOut

/-!
# SHA-224 and SHA-256 on PPC64LE, without secret residue

The streaming functions with frames and the one-shot functions, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers
(`Proof/Sha256/PostOut.lean`). HMAC, PBKDF2 and RSA call their code as
internal functions of their own (`vg_sha256_update_scratch`, …), not these.
The `init` functions read no memory, and need no clearing
(`Proof/Sha256/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha256_update`, which SHA-224 shares. -/
def updateReg : Registration Spec.Sha256.updateApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r7 Impl.Sha256.PPC64LE.Stream.update
      verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64))

/-- `vg_sha256_finalize`. -/
def finalizeReg : Registration Spec.Sha256.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64))

/-- `vg_sha224_finalize`. -/
def finalize224Reg : Registration Spec.Sha256.finalize224Api PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize224
      verified := Shared.finalize224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64))

/-- `vg_sha256_digest`. -/
def digest256Reg : Registration Spec.Sha256.digest256Api PPC64LE.target :=
  withScrub {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha256.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha256.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide)))

/-- `vg_sha224_digest`. -/
def digest224Reg : Registration Spec.Sha256.digest224Api PPC64LE.target :=
  withScrub {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha224.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha224.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide)))

/-- Each of them is scrubbed: `withScrub`'s side conditions hold. -/
example : updateReg.residue.isSome ∧ finalizeReg.residue.isSome ∧ finalize224Reg.residue.isSome ∧
    digest256Reg.residue.isSome ∧ digest224Reg.residue.isSome := by
  decide

end VG.Proof.Sha256.PPC64LE
