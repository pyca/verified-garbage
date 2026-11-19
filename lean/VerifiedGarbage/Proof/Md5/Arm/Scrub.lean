module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.Arm.Shared
public import VerifiedGarbage.Proof.Md5.PostOut
import VerifiedGarbage.Proof.Md5.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Md5.Arm.Shared
meta import VerifiedGarbage.Proof.Md5.PostOut
meta import VerifiedGarbage.Proof.Md5.Arm.Lit

/-!
# MD5 on ARMv7, without secret residue

`vg_md5_init` has no frames: it is registered followed by instructions that
set the registers a callee may change, but the result, and the flags to
constants (`Arm.Scrub.scrubReg`). `vg_md5_update` and `vg_md5_finalize` keep
their working space, and their caller's registers, in a frame of 128 bytes
(`Impl.StackScratch.Arm.withStackScratch`), the `stack` of their contracts,
and make no indirect call; their postconditions read the memory on return
only within their buffers (`Proof/Md5/PostOut.lean`): each is registered
followed by a wipe of those 128 bytes, and by the same instructions
(`Arm.Scrub.scrubRegF`). HMAC-MD5 and PBKDF2 call the streaming code under
internal names of their own (`vg_md5_init_core`, `vg_md5_update_scratch`,
`vg_md5_finalize_scratch`), not these functions.
-/

@[expose] public section

namespace VG.Proof.Md5.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

theorem init_noFrames : Impl.Md5.Arm.Stream.init.noFrames = true := by lit_decide

theorem frameOk_128 : FrameOk 128 := by decide

theorem update_noIcall :
    noIcall (Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update) = true := by
  lit_decide

theorem update_armStack :
    armStack (Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update) ≤ 128 := by
  lit_decide

theorem finalize_noIcall :
    noIcall (Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize) = true := by
  lit_decide

theorem finalize_armStack :
    armStack (Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize) ≤ 128 := by
  lit_decide

theorem updateOut :
    PostOut (Spec.Md5.updateContract Arm.abi 128) (Spec.Md5.updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Md5.updatePost_out 32)

theorem finalizeOut :
    PostOut (Spec.Md5.finalizeContract Arm.abi 128) (Spec.Md5.finalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Md5.finalizePost_out 32)

/-- `Spec.Md5.initApi`. -/
def initReg : Registration Spec.Md5.initApi target :=
  Arm.Scrub.scrubReg { code := Impl.Md5.Arm.Stream.init, verified := Shared.init } init_noFrames

/-- `Spec.Md5.updateApi`. -/
def updateReg : Registration Spec.Md5.updateApi target :=
  Arm.Scrub.scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update
      verified := Shared.update }
    update_armStack update_noIcall frameOk_128
    updateOut rfl

/-- `Spec.Md5.finalizeApi`. -/
def finalizeReg : Registration Spec.Md5.finalizeApi target :=
  Arm.Scrub.scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize
      verified := Shared.finalize }
    finalize_armStack finalize_noIcall frameOk_128
    finalizeOut rfl

end VG.Proof.Md5.Arm.Scrub
