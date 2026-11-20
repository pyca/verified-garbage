module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Md5.Arm.Stream
public import VerifiedGarbage.Proof.Md5.Arm.Shared
public import VerifiedGarbage.Proof.Md5.PostOut
import VerifiedGarbage.Proof.Md5.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Md5.Arm.Stream
meta import VerifiedGarbage.Proof.Md5.Arm.Shared
meta import VerifiedGarbage.Proof.Md5.PostOut
meta import VerifiedGarbage.Proof.Md5.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# MD5's functions on ARMv7, as emitted

`vg_md5_init`, `vg_md5_update` and `vg_md5_finalize` are MD5's streaming
functions with their cleanup (`Impl.Md5.Arm.Fn`): each returns with the
registers a callee may change set to constants, and `update` and `finalize`,
which keep their working space, and their caller's registers, in a frame of
128 bytes (`Impl.StackScratch.Arm.withStackScratch`), the `stack` of their
contracts, with those bytes zeroed. `Fn` below has the theorem of each, which
is what its registration binds.

`init` has no frame (`Arm.Scrub.verifiedScrubbed`). `update` and `finalize`
make no indirect call and use at most those 128 bytes (`CodeOk`, by
`lit_decide`), and their postconditions read the memory on return only within
their buffers (`Proof/Md5/PostOut.lean`). HMAC-MD5 and PBKDF2 call the
streaming code under internal names of their own (`vg_md5_init_core`,
`vg_md5_update_scratch`, `vg_md5_finalize_scratch`), not these functions.
-/

@[expose] public section

namespace VG.Proof.Md5.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

theorem init_noFrames : Impl.Md5.Arm.Stream.init.noFrames = true := by lit_decide

theorem frameOk_128 : FrameOk 128 := by decide

theorem update_ok :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update) 128 := by
  lit_decide

theorem finalize_ok :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize) 128 := by
  lit_decide

end VG.Proof.Md5.Arm.Scrub

namespace VG.Proof.Md5.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_md5_init`. -/
theorem init : VerifiedScrubbed target Impl.Md5.Arm.Fn.init (Spec.Md5.initContract abi) 0 :=
  verifiedScrubbed (api := Spec.Md5.initApi)
    { code := Impl.Md5.Arm.Stream.init, verified := Shared.init } Scrub.init_noFrames

/-- `vg_md5_update`. -/
theorem update : VerifiedScrubbed target Impl.Md5.Arm.Fn.update (Spec.Md5.updateContract abi 128) 0 :=
  verifiedScrubbedF (api := Spec.Md5.updateApi)
    { code := Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update
      verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.updatePost_out _))
    (scrubSideF_of Scrub.update_ok Scrub.frameOk_128 _)

/-- `vg_md5_finalize`. -/
theorem finalize :
    VerifiedScrubbed target Impl.Md5.Arm.Fn.finalize (Spec.Md5.finalizeContract abi 128) 0 :=
  verifiedScrubbedF (api := Spec.Md5.finalizeApi)
    { code := Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize
      verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.finalizePost_out _))
    (scrubSideF_of Scrub.finalize_ok Scrub.frameOk_128 _)

end VG.Proof.Md5.Arm.Fn
