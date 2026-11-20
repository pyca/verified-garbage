module

public import VerifiedGarbage.Proof.Sm3.PPC64LE.Stream.Init
public import VerifiedGarbage.Impl.Sm3.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm3.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM3 on PPC64LE, without secret residue

The streaming functions with frames, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Sm3/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sm3_update` as emitted (`Impl.Sm3.PPC64LE.Fn.update`) meets its contract
in constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm3.PPC64LE.Fn.update
      (Spec.Sm3.updateContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbed (api := Spec.Sm3.updateApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sm3.PPC64LE.Stream.update
      verified := Shared.update }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sm3_finalize` as emitted (`Impl.Sm3.PPC64LE.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm3.PPC64LE.Fn.finalize
      (Spec.Sm3.finalizeContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbed (api := Spec.Sm3.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sm3.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePostOut_local 64))
    (by dsimp only; lit_decide)


/-- `vg_sm3_init` needs no cleanup: it reads no memory, so what it leaves is a function of its
arguments. It meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sm3.PPC64LE.Stream.init
      (Spec.Sm3.initContract PPC64LE.abi) 0 :=
  ⟨Proof.Sm3.PPC64LE.Shared.init, Proof.Sm3.PPC64LE.Stream.init_noResidue _ _⟩

end VG.Proof.Sm3.PPC64LE
