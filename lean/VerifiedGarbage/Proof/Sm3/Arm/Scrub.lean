module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Sm3.Arm.Shared
public import VerifiedGarbage.Proof.Sm3.PostOut
import VerifiedGarbage.Proof.Sm3.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
meta import VerifiedGarbage.Proof.Sm3.Arm.Shared
meta import VerifiedGarbage.Proof.Sm3.PostOut
meta import VerifiedGarbage.Proof.Sm3.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM3 on ARMv7, without secret residue

As SHA-1 and SHA-2 (`Proof/MdStream/Arm/ShaScrub.lean`): `init` has no frame
and is registered with `Arm.Scrub.scrubReg`; `update` and `finalize` keep
their working space in a frame of 168 bytes (`withStackScratch`) and are
registered with `Arm.Scrub.scrubRegF`, which zeroes it. What `scrubRegF`
needs of their code follows from the compression function's, evaluated by
`lit_decide` on its literal, through the generic `update_scrubArm` and
`finalize_scrubArm`; their postconditions read the memory on return only
within their buffers (`Proof/Sm3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Proof.MdStream.Arm.ShaScrub

theorem compress_ok : ScrubOk Impl.Sm3.Arm.compress 0 := by lit_decide

theorem frameOk_168 : FrameOk 168 := by decide

/-- `vg_sm3_init`. -/
def initReg : Registration Spec.Sm3.initApi Arm.target :=
  scrubReg { code := Impl.Sm3.Arm.Stream.init, verified := Proof.Sm3.Arm.Shared.init } rfl

theorem update_ok : ScrubOk (Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update) 168 :=
  withStackScratch_scrubArm (n := 0) (update_scrubArm _ _ compress_ok)

theorem finalize_ok :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize) 168 :=
  withStackScratch_scrubArm (n := 0) (finalize_scrubArm _ _ compress_ok)

/-- `vg_sm3_update`. -/
def updateReg : Registration Spec.Sm3.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update
      verified := Proof.Sm3.Arm.Shared.update }
    update_ok.1 update_ok.2 frameOk_168
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePost_out _)) rfl

/-- `vg_sm3_finalize`. -/
def finalizeReg : Registration Spec.Sm3.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize
      verified := Proof.Sm3.Arm.Shared.finalize }
    finalize_ok.1 finalize_ok.2 frameOk_168
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePost_out _)) rfl

end VG.Proof.Sm3.Arm.Scrub
