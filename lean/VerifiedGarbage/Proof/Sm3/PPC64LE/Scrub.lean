module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm3.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM3 on PPC64LE, without secret residue

The streaming functions with frames, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Sm3/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sm3_update`. -/
def updateReg : Registration Spec.Sm3.updateApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sm3.PPC64LE.Stream.update
      verified := Shared.update }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sm3_finalize`. -/
def finalizeReg : Registration Spec.Sm3.finalizeApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sm3.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePostOut_local 64))
    (by dsimp only; lit_decide)


end VG.Proof.Sm3.PPC64LE
