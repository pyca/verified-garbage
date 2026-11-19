module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc4.Arm.Frame
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc4.Arm.Frame
meta import VerifiedGarbage.Proof.Rc4.Scratch
meta import VerifiedGarbage.Proof.Rc4.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC4 on ARMv7, without secret residue

`vg_rc4_init` and `vg_rc4_apply` on ARMv7 keep their 64 bytes of working
space in a frame (`withRegScratchWiped`) and make no call. Their
postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/Rc4/Scratch.lean` that the
other targets use too). Each is registered followed by a wipe of the stack
its contract reserves and by instructions that set the registers a callee
may change, but the result, and the flags to constants
(`Arm.Scrub.scrubRegF`).
-/

@[expose] public section

namespace VG.Proof.Rc4.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-! ## The postconditions -/

theorem initOut : PostOut (Spec.Rc4.initContract Arm.abi 64) (Spec.Rc4.initSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut : PostOut (Spec.Rc4.applyContract Arm.abi 64) (Spec.Rc4.applySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-! ## The code: its frames, and no indirect call -/

theorem init_code :
    armStack (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init) ≤ 64 ∧
      noIcall (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init) = true := by
  lit_decide

theorem apply_code :
    armStack (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply) ≤ 64 ∧
      noIcall (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply) = true := by
  lit_decide

/-! ## The registrations -/

/-- `vg_rc4_init`. -/
def initReg : Registration Spec.Rc4.initApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init
      verified := Proof.Rc4.Arm.init_framed }
    init_code.1 init_code.2 (by decide) initOut rfl

/-- `vg_rc4_apply`. -/
def applyReg : Registration Spec.Rc4.applyApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply
      verified := Proof.Rc4.Arm.apply_framed }
    apply_code.1 apply_code.2 (by decide) applyOut rfl

end VG.Proof.Rc4.Arm.Scrub
