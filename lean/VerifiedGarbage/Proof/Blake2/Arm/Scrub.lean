module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
public import VerifiedGarbage.Proof.Blake2.Arm.Blake2s
public import VerifiedGarbage.Proof.Blake2.Scratch
public import VerifiedGarbage.Proof.Blake2.PostOut
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
meta import VerifiedGarbage.Proof.Blake2.Arm.Blake2s
meta import VerifiedGarbage.Proof.Blake2.Scratch
meta import VerifiedGarbage.Proof.Blake2.PostOut
meta import VerifiedGarbage.Proof.Blake2.Arm.CompressB
meta import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# BLAKE2b and BLAKE2s on ARMv7, without secret residue

`init` has no frames: it is registered followed by instructions that set the
registers a callee may change, but the result, and the flags to constants
(`Arm.Scrub.scrubReg`). `update` and `finalize` keep their working space in a
frame of 592 bytes, under the 16 bytes of the compression function's stack
arguments, and make no indirect call. Their postconditions read the memory on
return only within their buffers (`Proof/Blake2/Scratch.lean`), so each is
registered followed by a wipe of the 608 bytes of stack its contract reserves
too (`Arm.Scrub.scrubRegF`).
-/

@[expose] public section

namespace VG.Proof.Blake2.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

theorem initB_noFrames : (Impl.Blake2.Arm.Stream.init Spec.Blake2.b).noFrames = true := by lit_decide

theorem initS_noFrames : (Impl.Blake2.Arm.Stream.init Spec.Blake2.s).noFrames = true := by lit_decide

theorem updateB_noIcall : noIcall (Impl.StackScratch.Arm.withStackScratch 592 2
    (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)) = true := by
  lit_decide

theorem updateB_armStack : armStack (Impl.StackScratch.Arm.withStackScratch 592 2
    (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)) ≤ 16 + 592 := by
  lit_decide

theorem finalizeB_noIcall : noIcall (Impl.StackScratch.Arm.withStackScratch 592 1
    (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)) = true := by
  lit_decide

theorem finalizeB_armStack : armStack (Impl.StackScratch.Arm.withStackScratch 592 1
    (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)) ≤ 16 + 592 := by
  lit_decide

theorem updateS_noIcall : noIcall (Impl.StackScratch.Arm.withStackScratch 592 2
    (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)) = true := by
  lit_decide

theorem updateS_armStack : armStack (Impl.StackScratch.Arm.withStackScratch 592 2
    (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)) ≤ 16 + 592 := by
  lit_decide

theorem finalizeS_noIcall : noIcall (Impl.StackScratch.Arm.withStackScratch 592 1
    (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)) = true := by
  lit_decide

theorem finalizeS_armStack : armStack (Impl.StackScratch.Arm.withStackScratch 592 1
    (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)) ≤ 16 + 592 := by
  lit_decide

theorem frameOk_608 : FrameOk (16 + 592) := by decide

/-- `vg_blake2b_init`. -/
def initBReg : Registration Spec.Blake2.initBApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Blake2.Arm.Stream.init Spec.Blake2.b
      verified := Proof.Blake2.ArmB.initB_verified }
    initB_noFrames

/-- `vg_blake2b_update`. -/
def updateBReg : Registration Spec.Blake2.updateBApi target :=
  Arm.Scrub.scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 592 2
        (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      verified := Proof.Blake2.ArmB.updateB_framed }
    updateB_armStack updateB_noIcall frameOk_608
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out 32)) rfl

/-- `vg_blake2b_finalize`. -/
def finalizeBReg : Registration Spec.Blake2.finalizeBApi target :=
  Arm.Scrub.scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 592 1
        (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      verified := Proof.Blake2.ArmB.finalizeB_framed }
    finalizeB_armStack finalizeB_noIcall frameOk_608
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out 32)) rfl

/-- `vg_blake2s_init`. -/
def initSReg : Registration Spec.Blake2.initSApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Blake2.Arm.Stream.init Spec.Blake2.s
      verified := Proof.Blake2.Arm.Blake2s.initS_verified }
    initS_noFrames

/-- `vg_blake2s_update`. -/
def updateSReg : Registration Spec.Blake2.updateSApi target :=
  Arm.Scrub.scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 592 2
        (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      verified := Proof.Blake2.Arm.Blake2s.updateS_framed }
    updateS_armStack updateS_noIcall frameOk_608
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out 32)) rfl

/-- `vg_blake2s_finalize`. -/
def finalizeSReg : Registration Spec.Blake2.finalizeSApi target :=
  Arm.Scrub.scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 592 1
        (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      verified := Proof.Blake2.Arm.Blake2s.finalizeS_framed }
    finalizeS_armStack finalizeS_noIcall frameOk_608
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out 32)) rfl

end VG.Proof.Blake2.Arm.Scrub
