module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Rc2.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame
meta import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Chained
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Proof.Rc2.CbcScratch
meta import VerifiedGarbage.Proof.Rc2.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC2 on ARMv7, without secret residue

RC2's three public functions on ARMv7 keep their working space in a frame
(`withStackScratchWiped`: `init`'s 592 bytes, CBC's 528), call the key
expansion and the block functions by name, and make no indirect call. Their
postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/Rc2/Scratch.lean` and
`Proof/Rc2/CbcScratch.lean` that the other targets use too). Each is
registered followed by a wipe of the stack its contract reserves and by
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Arm.Scrub.scrubRegF`). The functions they call are
internal, so they keep their code as it is verified.
-/

@[expose] public section

namespace VG.Proof.Rc2.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Impl.Rc2 (piConsts)

/-! ## The postconditions -/

theorem cbcInitOut :
    PostOut (Spec.Rc2.cbcInitContract (Arm.abi.withConsts piConsts) 600) (Spec.Rc2.cbcInitSig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts piConsts) (Proof.Rc2.cbcInitPostOut_local _)

theorem cbcEncryptChainedOut :
    PostOut (Spec.Rc2.cbcEncryptChainedContract Arm.abi 528) (Spec.Rc2.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcEncChainedPostOut_local (pb := 32))

theorem cbcDecryptChainedOut :
    PostOut (Spec.Rc2.cbcDecryptChainedContract Arm.abi 528) (Spec.Rc2.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcDecChainedPostOut_local (pb := 32))

/-! ## The code: its frames, and no indirect call -/

theorem init_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init) ≤ 600 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init) = true := by
  lit_decide

theorem encrypt_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt) ≤ 528 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt) = true := by
  lit_decide

theorem decrypt_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt) ≤ 528 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt) = true := by
  lit_decide

/-! ## The registrations -/

/-- `vg_rc2_cbc_init`. -/
def cbcInitReg : Registration Spec.Rc2.cbcInitApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init
      verified := Proof.Rc2.Arm.Stream.init_framed }
    init_code.1 init_code.2 (by decide) cbcInitOut rfl

/-- `vg_rc2_cbc_encrypt_chained`. -/
def cbcEncryptChainedReg : Registration Spec.Rc2.cbcEncryptChainedApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt
      verified := Proof.Rc2.Arm.Cbc.encryptChained_framed }
    encrypt_code.1 encrypt_code.2 (by decide) cbcEncryptChainedOut rfl

/-- `vg_rc2_cbc_decrypt_chained`. -/
def cbcDecryptChainedReg : Registration Spec.Rc2.cbcDecryptChainedApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt
      verified := Proof.Rc2.Arm.Cbc.decryptChained_framed }
    decrypt_code.1 decrypt_code.2 (by decide) cbcDecryptChainedOut rfl

end VG.Proof.Rc2.Arm.Scrub
