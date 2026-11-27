module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Sm3.Arm.Stream
public import VerifiedGarbage.Proof.Sm3.Arm.Shared
public import VerifiedGarbage.Proof.Sm3.PostOut
import VerifiedGarbage.Proof.Sm3.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Sm3.Arm.Stream
meta import VerifiedGarbage.Proof.Sm3.Arm.Shared
meta import VerifiedGarbage.Proof.Sm3.PostOut
meta import VerifiedGarbage.Proof.Sm3.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM3's functions on ARMv7, as emitted

`vg_sm3_init`, `vg_sm3_update` and `vg_sm3_finalize` are SM3's streaming
functions with their cleanup (`Impl.Sm3.Arm.Fn`): each returns with the
registers a callee may change set to constants, and `update` and `finalize`,
which keep their working space in a frame of 168 bytes
(`withStackScratch`), with those bytes zeroed. `Fn` below has the theorem of
each: it meets its contract in constant time (`Proof.Sm3.Arm.Shared`) and
returns without secret residue (`VerifiedScrubbed`), which is what its
registration binds.

`init` has no frame (`Arm.Scrub.verifiedScrubbed`). What the cleanup of
`update` and `finalize` needs of their code (`Arm.Scrub.scrubSideF`) follows
from the compression function's (`CodeOk`, evaluated by `lit_decide` on its
literal) through the generic `update_scrubArm` and `finalize_scrubArm`; their
postconditions read the memory on return only within their buffers
(`Proof/Sm3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Proof.MdStream.Arm.ShaScrub

theorem compress_ok : ScrubOk Impl.Sm3.Arm.compress 0 := by lit_decide

theorem frameOk_168 : FrameOk 168 := by decide

theorem update_ok : ScrubOk (Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update) 168 :=
  withStackScratch_scrubArm (n := 0) (update_scrubArm _ _ compress_ok)

theorem finalize_ok :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize) 168 :=
  withStackScratch_scrubArm (n := 0) (finalize_scrubArm _ _ compress_ok)

end VG.Proof.Sm3.Arm.Scrub

namespace VG.Proof.Sm3.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_sm3_init`. -/
theorem init : VerifiedScrubbed target Impl.Sm3.Arm.Fn.init (Spec.Sm3.initContract abi) 0 :=
  verifiedScrubbed (api := Spec.Sm3.initApi)
    { code := Impl.Sm3.Arm.Stream.init, verified := Proof.Sm3.Arm.Shared.init } rfl

/-- `vg_sm3_update`. -/
theorem update : VerifiedScrubbed target Impl.Sm3.Arm.Fn.update (Spec.Sm3.updateContract abi 168) 0 :=
  verifiedScrubbedAll (api := Spec.Sm3.updateApi)
    { code := Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update
      verified := Proof.Sm3.Arm.Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePost_out _))
    (scrubSideF_of Scrub.update_ok Scrub.frameOk_168 _)

/-- `vg_sm3_finalize`. -/
theorem finalize : VerifiedScrubbed target Impl.Sm3.Arm.Fn.finalize (Spec.Sm3.finalizeContract abi 168) 0 :=
  verifiedScrubbedAll (api := Spec.Sm3.finalizeApi)
    { code := Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize
      verified := Proof.Sm3.Arm.Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePost_out _))
    (scrubSideF_of Scrub.finalize_ok Scrub.frameOk_168 _)

end VG.Proof.Sm3.Arm.Fn
