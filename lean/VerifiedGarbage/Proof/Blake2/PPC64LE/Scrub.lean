module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.Scratch
public import VerifiedGarbage.Proof.Blake2.PostOut
import VerifiedGarbage.Proof.Blake2.PPC64LE.Lit
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# BLAKE2b and BLAKE2s on PPC64LE, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.scrubOf`), which clears the volatile registers they write
and the stack their frames used: `update` and `finalize` keep their working
space in a 608-byte frame they do not wipe themselves (`withStackScratch`),
and a 48-byte frame below it that saves their return address around the
calls of the compression function, 656 bytes in all, which the tail zeroes with `dcbz`; `init` has no frame. Their postconditions
read the memory on return only within their buffers
(`Proof/Blake2/PostOut.lean`, `Proof/Blake2/Scratch.lean`), as on RISC-V
(`Proof/Blake2/RISCV64/Scrub.lean`). Argon2 calls `vg_blake2b_init`'s code
as the internal `vg_blake2b_init_core` (`Impl.Argon2.PPC64LE.HPrime.initName`),
and BLAKE2's update and finalize as their own internal `_scratch` functions.
-/

@[expose] public section

namespace VG.Proof.Blake2.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_blake2b_init`. -/
def initBReg : Registration Spec.Blake2.initBApi PPC64LE.target :=
  scrubOf {
      code := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.b
      verified := Proof.Blake2.PPC64LE.Stream.initB_verified }
    0 ⟨false, false, [.r5, .r6, .r9, .r10, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initBPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2b_update`. -/
def updateBReg : Registration Spec.Blake2.updateBApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.b)
      verified := Proof.Blake2.PPC64LE.Stream.updateB_framed }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2b_finalize`. -/
def finalizeBReg : Registration Spec.Blake2.finalizeBApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.b)
      verified := Proof.Blake2.PPC64LE.Stream.finalizeB_framed }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2s_init`. -/
def initSReg : Registration Spec.Blake2.initSApi PPC64LE.target :=
  scrubOf {
      code := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.s
      verified := Proof.Blake2.PPC64LE.Stream.initS_verified }
    0 ⟨false, false, [.r5, .r6, .r9, .r10, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initSPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2s_update`. -/
def updateSReg : Registration Spec.Blake2.updateSApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.s)
      verified := Proof.Blake2.PPC64LE.Stream.updateS_framed }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2s_finalize`. -/
def finalizeSReg : Registration Spec.Blake2.finalizeSApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.s)
      verified := Proof.Blake2.PPC64LE.Stream.finalizeS_framed }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out 64))
    (by dsimp only; lit_decide)

end VG.Proof.Blake2.PPC64LE.Scrub
