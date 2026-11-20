module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.CmacAes.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.CmacAes.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming AES-CMAC on ARMv7, without secret residue

`vg_cmac_aes_init`, `vg_cmac_aes_absorb` and `vg_cmac_aes_finish` keep their
working space, and the functions they call their frames, within the stack
their contracts reserve, and make no indirect call (evaluated by
`lit_decide`). Their postconditions read the memory on return only within
the state and the tag (`Arm.Scrub.PostOut`), by the target-independent
lemmas of `Proof/CmacAes/Stream/Scratch.lean`, as on x86
(`Proof/CmacAes/Stream/X86/Scrub.lean`). Each is emitted followed by a wipe
of that stack and by instructions that set the registers a callee may
change, and the flags, to constants (`Impl.CmacAes.Arm.Fn`), and `Fn` below
states that it returns without secret residue
(`Arm.Scrub.verifiedScrubbedF`), which is what its registration binds.
`init`'s contract reserves 2312 bytes, which is no frame size of the model
(`FrameOk`), so it is proven with the next one, 2320
(`Arm.Scrub.Verified.stack_le`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.CmacAes.Stream.Arm

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.aesInitContract Arm.abi stack) (Spec.Cmac.aesInitSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacAes.Stream.initPostOut_local _)

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.aesAbsorbContract Arm.abi stack) (Spec.Cmac.aesAbsorbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacAes.Stream.absorbPostOut_local _)

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.aesFinishContract Arm.abi stack) (Spec.Cmac.aesFinishSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.CmacAes.Stream.finishPostOut_local _)

/-! ## `init` with the next frame size -/

theorem initSat2320 : ∃ s, (Spec.Cmac.aesInitContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.CmacAes.Stream.Arm.initFrameSat, Proof.CmacAes.Stream.Arm.initSat]
    using Proof.CmacAes.Stream.Arm.initFrameSat

theorem init_framed2320 : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2304 .r3 init)
    (Spec.Cmac.aesInitContract Arm.abi 2320) :=
  Verified.stack_le (by decide) Proof.CmacAes.Stream.Arm.init_framed initSat2320

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_2320 : FrameOk 2320 := by decide
theorem frameOk_2336 : FrameOk 2336 := by decide

theorem init_code : CodeOk (Impl.StackScratch.Arm.withRegScratch 2304 .r3 init) 2320 := by
  lit_decide

theorem absorb_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 2320 2 absorb) 2336 := by
  lit_decide

theorem finish_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 2320 1 finish) 2336 := by
  lit_decide

end VG.Proof.CmacAes.Arm.Scrub

namespace VG.Proof.CmacAes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- `vg_cmac_aes_init`. -/
theorem init : VerifiedScrubbed target Impl.CmacAes.Arm.Fn.init (Spec.Cmac.aesInitContract abi 2320) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.aesInitApi)
    { code := Impl.StackScratch.Arm.withRegScratch 2304 .r3 Impl.CmacAes.Stream.Arm.init
      verified := Scrub.init_framed2320 }
    (Scrub.initOut _) (scrubSideF_of Scrub.init_code Scrub.frameOk_2320 _)

/-- `vg_cmac_aes_absorb`. -/
theorem absorb : VerifiedScrubbed target Impl.CmacAes.Arm.Fn.absorb (Spec.Cmac.aesAbsorbContract abi 2336) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.aesAbsorbApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2320 2 Impl.CmacAes.Stream.Arm.absorb
      verified := Proof.CmacAes.Stream.Arm.absorb_framed }
    (Scrub.absorbOut _) (scrubSideF_of Scrub.absorb_code Scrub.frameOk_2336 _)

/-- `vg_cmac_aes_finish`. -/
theorem finish : VerifiedScrubbed target Impl.CmacAes.Arm.Fn.finish (Spec.Cmac.aesFinishContract abi 2336) 0 :=
  verifiedScrubbedF (api := Spec.Cmac.aesFinishApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2320 1 Impl.CmacAes.Stream.Arm.finish
      verified := Proof.CmacAes.Stream.Arm.finish_framed }
    (Scrub.finishOut _) (scrubSideF_of Scrub.finish_code Scrub.frameOk_2336 _)

end VG.Proof.CmacAes.Arm.Fn
