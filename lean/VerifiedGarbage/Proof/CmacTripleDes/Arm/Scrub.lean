module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.CmacTripleDes.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Frame
import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Frame
meta import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming TDEA-CMAC on ARMv7, without secret residue

`vg_cmac_triple_des_stream_init`, `vg_cmac_triple_des_absorb` and
`vg_cmac_triple_des_finish` keep their working space, and the frames of the
code they inline, within the stack their contracts reserve, and make no
indirect call (evaluated by `lit_decide`). Their postconditions read the
memory on return only within the state and the tag (`Arm.Scrub.PostOut`), by
the target-independent lemmas of `Proof/CmacTripleDes/StreamScratch.lean`.
Each is emitted followed by a wipe of that stack and by instructions that set
the registers a callee may change, and the flags, to constants
(`Impl.CmacTripleDes.Arm.Fn`), and `Fn` below states that it returns without
secret residue (`Arm.Scrub.verifiedScrubbedF`), which is what its
registration binds. The contracts of `absorb` and `finish` reserve 708 and
660 bytes, which are no frame sizes of the model (`FrameOk`), so they are
proven with the next ones, 712 and 664 (`Arm.Scrub.Verified.stack_le`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.CmacTripleDes.Stream.Arm
open VG.Proof.CmacTripleDes.Stream.Arm (countArm)

/-! ## Postconditions -/

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesStreamInitContract Arm.abi stack) (Spec.Cmac.tdesStreamInitSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacTripleDes.Stream.streamInitPostOut_local _)

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesAbsorbContract Arm.abi stack) (Spec.Cmac.tdesAbsorbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacTripleDes.Stream.absorbPostOut_local _)

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.tdesFinishContract Arm.abi stack) (Spec.Cmac.tdesFinishSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacTripleDes.Stream.finishPostOut_local _)

/-! ## `absorb` and `finish` with the next frame sizes -/

theorem absorbSat712 : ∃ s, (Spec.Cmac.tdesAbsorbContract Arm.abi 712).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.CmacTripleDes.Stream.Arm.absorbFrameSat, Proof.CmacTripleDes.Stream.Arm.absorbSat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Proof.CmacTripleDes.Stream.Arm.absorbFrameSat

theorem finishSat664 : ∃ s, (Spec.Cmac.tdesFinishContract Arm.abi 664).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.CmacTripleDes.Stream.Arm.finishFrameSat, Proof.CmacTripleDes.Stream.Arm.finishSat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Proof.CmacTripleDes.Stream.Arm.finishFrameSat

theorem absorb_framed712 : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 704 2 absorb)
    (Spec.Cmac.tdesAbsorbContract Arm.abi 712) :=
  Verified.stack_le (by decide) Proof.CmacTripleDes.Stream.Arm.absorb_framed absorbSat712

theorem finish_framed664 : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 656 1 finish)
    (Spec.Cmac.tdesFinishContract Arm.abi 664) :=
  Verified.stack_le (by decide) Proof.CmacTripleDes.Stream.Arm.finish_framed finishSat664

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_640 : FrameOk 640 := by decide
theorem frameOk_712 : FrameOk 712 := by decide
theorem frameOk_664 : FrameOk 664 := by decide

theorem streamInit_code : CodeOk (Impl.StackScratch.Arm.withRegScratch 640 .r3 streamInit) 640 := by
  lit_decide

theorem absorb_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 704 2 absorb) 712 := by
  lit_decide

theorem finish_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 656 1 finish) 664 := by
  lit_decide

end VG.Proof.CmacTripleDes.Arm.Scrub

namespace VG.Proof.CmacTripleDes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- `vg_cmac_triple_des_stream_init`. -/
theorem streamInit :
    VerifiedScrubbed target Impl.CmacTripleDes.Arm.Fn.streamInit (Spec.Cmac.tdesStreamInitContract abi 640) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.tdesStreamInitApi)
    { code := Impl.StackScratch.Arm.withRegScratch 640 .r3 Impl.CmacTripleDes.Stream.Arm.streamInit
      verified := Proof.CmacTripleDes.Stream.Arm.init_framed }
    (Scrub.streamInitOut _) (scrubSideF_of Scrub.streamInit_code Scrub.frameOk_640 _)

/-- `vg_cmac_triple_des_absorb`. -/
theorem absorb :
    VerifiedScrubbed target Impl.CmacTripleDes.Arm.Fn.absorb (Spec.Cmac.tdesAbsorbContract abi 712) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.tdesAbsorbApi)
    { code := Impl.StackScratch.Arm.withStackScratch 704 2 Impl.CmacTripleDes.Stream.Arm.absorb
      verified := Scrub.absorb_framed712 }
    (Scrub.absorbOut _) (scrubSideF_of Scrub.absorb_code Scrub.frameOk_712 _)

/-- `vg_cmac_triple_des_finish`. -/
theorem finish :
    VerifiedScrubbed target Impl.CmacTripleDes.Arm.Fn.finish (Spec.Cmac.tdesFinishContract abi 664) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.tdesFinishApi)
    { code := Impl.StackScratch.Arm.withStackScratch 656 1 Impl.CmacTripleDes.Stream.Arm.finish
      verified := Scrub.finish_framed664 }
    (Scrub.finishOut _) (scrubSideF_of Scrub.finish_code Scrub.frameOk_664 _)

end VG.Proof.CmacTripleDes.Arm.Fn
