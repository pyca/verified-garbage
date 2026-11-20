module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Rc2.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Rc2.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Rc2.Arm.Fn
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
emitted followed by a wipe of the stack its contract reserves and by
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Rc2.Arm.Fn`), and `Fn` below states
that each returns without secret residue (`Arm.Scrub.verifiedScrubbedF`),
which is what its registration binds. The functions they call are
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
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init) 600 := by
  lit_decide

theorem encrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt) 528 := by
  lit_decide

theorem decrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt) 528 := by
  lit_decide

end VG.Proof.Rc2.Arm.Scrub

namespace VG.Proof.Rc2.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Impl.Rc2 (piConsts)

/-- `vg_rc2_cbc_init`. -/
theorem cbcInit :
    VerifiedScrubbed target Impl.Rc2.Arm.Fn.cbcInit (Spec.Rc2.cbcInitContract (Arm.abi.withConsts piConsts) 600) 32 :=
  verifiedScrubbedF (api := Spec.Rc2.cbcInitApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init
      verified := Proof.Rc2.Arm.Stream.init_framed }
    Scrub.cbcInitOut (scrubSideF_of Scrub.init_code (by decide) _)

/-- `vg_rc2_cbc_encrypt_chained`. -/
theorem cbcEncryptChained :
    VerifiedScrubbed target Impl.Rc2.Arm.Fn.cbcEncryptChained (Spec.Rc2.cbcEncryptChainedContract Arm.abi 528) 0 :=
  verifiedScrubbedF (api := Spec.Rc2.cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt
      verified := Proof.Rc2.Arm.Cbc.encryptChained_framed }
    Scrub.cbcEncryptChainedOut (scrubSideF_of Scrub.encrypt_code (by decide) _)

/-- `vg_rc2_cbc_decrypt_chained`. -/
theorem cbcDecryptChained :
    VerifiedScrubbed target Impl.Rc2.Arm.Fn.cbcDecryptChained (Spec.Rc2.cbcDecryptChainedContract Arm.abi 528) 0 :=
  verifiedScrubbedF (api := Spec.Rc2.cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt
      verified := Proof.Rc2.Arm.Cbc.decryptChained_framed }
    Scrub.cbcDecryptChainedOut (scrubSideF_of Scrub.decrypt_code (by decide) _)

end VG.Proof.Rc2.Arm.Fn
