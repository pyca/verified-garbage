module

public import VerifiedGarbage.Impl.Rc2.Arm.Stream
public import VerifiedGarbage.Impl.Rc2.Arm.Cbc
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# RC2 on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/Rc2/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Rc2.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_rc2_cbc_init`. -/
def cbcInit : Prog isa := scrubF 32 600 (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init)

/-- `vg_rc2_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubF 0 528 (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt)

/-- `vg_rc2_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubF 0 528 (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt)

end VG.Impl.Rc2.Arm.Fn
