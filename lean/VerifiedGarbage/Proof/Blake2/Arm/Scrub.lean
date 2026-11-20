module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
public import VerifiedGarbage.Proof.Blake2.Arm.Blake2s
public import VerifiedGarbage.Proof.Blake2.Scratch
public import VerifiedGarbage.Proof.Blake2.PostOut
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
meta import VerifiedGarbage.Proof.Blake2.Arm.Blake2s
meta import VerifiedGarbage.Proof.Blake2.Scratch
meta import VerifiedGarbage.Proof.Blake2.PostOut
meta import VerifiedGarbage.Proof.Blake2.Arm.CompressB
meta import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# BLAKE2b and BLAKE2s on ARMv7, as emitted

BLAKE2b's and BLAKE2s's streaming functions with their cleanup
(`Impl.Blake2.Arm.Fn`): `init` has no frames, and its cleanup sets the
registers a callee may change, and the flags, to constants
(`Arm.Scrub.verifiedScrubbed`). `update` and `finalize` keep their working
space in a frame of 592 bytes, under the 16 bytes of the compression
function's stack arguments, and make no indirect call (`CodeOk`, by
`lit_decide`). Their postconditions read the memory on return only within
their buffers (`Proof/Blake2/Scratch.lean`), so their cleanup zeroes the 608
bytes of stack their contracts reserve too
(`Arm.Scrub.verifiedScrubbedF`). `Fn` below has the theorem of each, which
is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Blake2.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

theorem initB_noFrames : (Impl.Blake2.Arm.Stream.init Spec.Blake2.b).noFrames = true := by lit_decide

theorem initS_noFrames : (Impl.Blake2.Arm.Stream.init Spec.Blake2.s).noFrames = true := by lit_decide

theorem updateB_ok : CodeOk (Impl.StackScratch.Arm.withStackScratch 592 2
    (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)) (16 + 592) := by
  lit_decide

theorem finalizeB_ok : CodeOk (Impl.StackScratch.Arm.withStackScratch 592 1
    (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)) (16 + 592) := by
  lit_decide

theorem updateS_ok : CodeOk (Impl.StackScratch.Arm.withStackScratch 592 2
    (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)) (16 + 592) := by
  lit_decide

theorem finalizeS_ok : CodeOk (Impl.StackScratch.Arm.withStackScratch 592 1
    (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)) (16 + 592) := by
  lit_decide

theorem frameOk_608 : FrameOk (16 + 592) := by decide

end VG.Proof.Blake2.Arm.Scrub

namespace VG.Proof.Blake2.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_blake2b_init`. -/
theorem initB : VerifiedScrubbed target Impl.Blake2.Arm.Fn.initB (Spec.Blake2.initBContract abi) 0 :=
  verifiedScrubbed (api := Spec.Blake2.initBApi)
    { code := Impl.Blake2.Arm.Stream.init Spec.Blake2.b
      verified := Proof.Blake2.ArmB.initB_verified }
    Scrub.initB_noFrames

/-- `vg_blake2b_update`. -/
theorem updateB :
    VerifiedScrubbed target Impl.Blake2.Arm.Fn.updateB (Spec.Blake2.updateBContract abi (16 + 592)) 0 :=
  verifiedScrubbedF (api := Spec.Blake2.updateBApi)
    { code := Impl.StackScratch.Arm.withStackScratch 592 2
        (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      verified := Proof.Blake2.ArmB.updateB_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out 32))
    (scrubSideF_of Scrub.updateB_ok Scrub.frameOk_608 _)

/-- `vg_blake2b_finalize`. -/
theorem finalizeB :
    VerifiedScrubbed target Impl.Blake2.Arm.Fn.finalizeB (Spec.Blake2.finalizeBContract abi (16 + 592)) 0 :=
  verifiedScrubbedF (api := Spec.Blake2.finalizeBApi)
    { code := Impl.StackScratch.Arm.withStackScratch 592 1
        (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      verified := Proof.Blake2.ArmB.finalizeB_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out 32))
    (scrubSideF_of Scrub.finalizeB_ok Scrub.frameOk_608 _)

/-- `vg_blake2s_init`. -/
theorem initS : VerifiedScrubbed target Impl.Blake2.Arm.Fn.initS (Spec.Blake2.initSContract abi) 0 :=
  verifiedScrubbed (api := Spec.Blake2.initSApi)
    { code := Impl.Blake2.Arm.Stream.init Spec.Blake2.s
      verified := Proof.Blake2.Arm.Blake2s.initS_verified }
    Scrub.initS_noFrames

/-- `vg_blake2s_update`. -/
theorem updateS :
    VerifiedScrubbed target Impl.Blake2.Arm.Fn.updateS (Spec.Blake2.updateSContract abi (16 + 592)) 0 :=
  verifiedScrubbedF (api := Spec.Blake2.updateSApi)
    { code := Impl.StackScratch.Arm.withStackScratch 592 2
        (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      verified := Proof.Blake2.Arm.Blake2s.updateS_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out 32))
    (scrubSideF_of Scrub.updateS_ok Scrub.frameOk_608 _)

/-- `vg_blake2s_finalize`. -/
theorem finalizeS :
    VerifiedScrubbed target Impl.Blake2.Arm.Fn.finalizeS (Spec.Blake2.finalizeSContract abi (16 + 592)) 0 :=
  verifiedScrubbedF (api := Spec.Blake2.finalizeSApi)
    { code := Impl.StackScratch.Arm.withStackScratch 592 1
        (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      verified := Proof.Blake2.Arm.Blake2s.finalizeS_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out 32))
    (scrubSideF_of Scrub.finalizeS_ok Scrub.frameOk_608 _)

end VG.Proof.Blake2.Arm.Fn
