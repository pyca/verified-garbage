module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sha1.Scratch
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.MdStream.DigestScratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-1 on PPC64LE, without secret residue

The streaming functions with frames and the one-shot digest, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Sha1/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha1.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha1_update`. -/
def updateReg : Registration Spec.Sha1.updateApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sha1.PPC64LE.Stream.update
      verified := Shared.update }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sha1_finalize`. -/
def finalizeReg : Registration Spec.Sha1.finalizeApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sha1.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sha1_digest`. -/
def digestReg : Registration Spec.Sha1.digestApi PPC64LE.target :=
  scrubOf {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha1.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha1.digest }
    496 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 20 Spec.Sha1.hash 64))
    (by dsimp only; lit_decide)


end VG.Proof.Sha1.PPC64LE
