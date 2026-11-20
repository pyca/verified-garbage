module

public import VerifiedGarbage.Impl.Blake2.PPC64LE.Fn
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
(`PPC64LE.Scrub.verifiedScrubbed`), which clears the volatile registers they write
and the stack their frames used: `update` and `finalize` keep their working
space, the 152 bytes of scratch they use, in a 192-byte frame they do not
wipe themselves (`withStackScratch`), and a 48-byte frame below it that saves
their return address around the calls of the compression function, 240 bytes
in all, which the tail zeroes; `init` has no frame. Their postconditions
read the memory on return only within their buffers
(`Proof/Blake2/PostOut.lean`, `Proof/Blake2/Scratch.lean`), as on RISC-V
(`Proof/Blake2/RISCV64/Scrub.lean`). Argon2 calls `vg_blake2b_init`'s code
as the internal `vg_blake2b_init_core` (`Impl.Argon2.PPC64LE.HPrime.initName`),
and BLAKE2's update and finalize as their own internal `_scratch` functions.
-/

@[expose] public section

namespace VG.Proof.Blake2.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_blake2b_init` as emitted (`Impl.Blake2.PPC64LE.Fn.initB`) meets its
contract in constant time and returns without secret residue. -/
theorem initB_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blake2.PPC64LE.Fn.initB
      (Spec.Blake2.initBContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Blake2.initBApi) {
      code := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.b
      verified := Proof.Blake2.PPC64LE.Stream.initB_verified }
    0 ⟨false, false, [.r5, .r6, .r9, .r10, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initBPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2b_update` as emitted (`Impl.Blake2.PPC64LE.Fn.updateB`) meets its
contract in constant time and returns without secret residue. -/
theorem updateB_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blake2.PPC64LE.Fn.updateB
      (Spec.Blake2.updateBContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbed (api := Spec.Blake2.updateBApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.b)
      verified := Proof.Blake2.PPC64LE.Stream.updateB_framed }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2b_finalize` as emitted (`Impl.Blake2.PPC64LE.Fn.finalizeB`) meets
its contract in constant time and returns without secret residue. -/
theorem finalizeB_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blake2.PPC64LE.Fn.finalizeB
      (Spec.Blake2.finalizeBContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbed (api := Spec.Blake2.finalizeBApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.b)
      verified := Proof.Blake2.PPC64LE.Stream.finalizeB_framed }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2s_init` as emitted (`Impl.Blake2.PPC64LE.Fn.initS`) meets its
contract in constant time and returns without secret residue. -/
theorem initS_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blake2.PPC64LE.Fn.initS
      (Spec.Blake2.initSContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Blake2.initSApi) {
      code := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.s
      verified := Proof.Blake2.PPC64LE.Stream.initS_verified }
    0 ⟨false, false, [.r5, .r6, .r9, .r10, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initSPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2s_update` as emitted (`Impl.Blake2.PPC64LE.Fn.updateS`) meets its
contract in constant time and returns without secret residue. -/
theorem updateS_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blake2.PPC64LE.Fn.updateS
      (Spec.Blake2.updateSContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbed (api := Spec.Blake2.updateSApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.s)
      verified := Proof.Blake2.PPC64LE.Stream.updateS_framed }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_blake2s_finalize` as emitted (`Impl.Blake2.PPC64LE.Fn.finalizeS`) meets
its contract in constant time and returns without secret residue. -/
theorem finalizeS_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blake2.PPC64LE.Fn.finalizeS
      (Spec.Blake2.finalizeSContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbed (api := Spec.Blake2.finalizeSApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.s)
      verified := Proof.Blake2.PPC64LE.Stream.finalizeS_framed }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out 64))
    (by dsimp only; lit_decide)

end VG.Proof.Blake2.PPC64LE.Scrub
