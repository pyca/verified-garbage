module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.PPC64LE.Shared
public import VerifiedGarbage.Proof.Md5.Scratch

/-!
# MD5 on PPC64LE, without secret residue

The streaming functions with frames, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Md5/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_md5_update`. -/
def updateReg : Registration Spec.Md5.updateApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r7 Impl.Md5.PPC64LE.Stream.update
      verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.updatePostOut_local 64))

/-- `vg_md5_finalize`. -/
def finalizeReg : Registration Spec.Md5.finalizeApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.Md5.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.finalizePostOut_local 64))


end VG.Proof.Md5.PPC64LE
