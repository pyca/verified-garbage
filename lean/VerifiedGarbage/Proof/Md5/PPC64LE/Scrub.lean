module

public import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Init
public import VerifiedGarbage.Impl.Md5.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.PPC64LE.Shared
public import VerifiedGarbage.Proof.Md5.Scratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# MD5 on PPC64LE, without secret residue

The streaming functions with frames, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Md5/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_md5_update` as emitted (`Impl.Md5.PPC64LE.Fn.update`) meets its contract
in constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Md5.PPC64LE.Fn.update
      (Spec.Md5.updateContract PPC64LE.abi (48 + 144)) 0 :=
  verifiedScrubbed (api := Spec.Md5.updateApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r7 Impl.Md5.PPC64LE.Stream.update
      verified := Shared.update }
    192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.updatePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_md5_finalize` as emitted (`Impl.Md5.PPC64LE.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Md5.PPC64LE.Fn.finalize
      (Spec.Md5.finalizeContract PPC64LE.abi (48 + 144)) 0 :=
  verifiedScrubbed (api := Spec.Md5.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.Md5.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.finalizePostOut_local 64))
    (by dsimp only; lit_decide)


/-- `vg_md5_init` needs no cleanup: it reads no memory, so what it leaves is a function of its
arguments. It meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Md5.PPC64LE.Stream.init
      (Spec.Md5.initContract PPC64LE.abi) 0 :=
  ⟨Proof.Md5.PPC64LE.Shared.init, Proof.Md5.PPC64LE.Stream.init_noResidue _ _⟩

end VG.Proof.Md5.PPC64LE
