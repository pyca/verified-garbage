module

public import VerifiedGarbage.Impl.Rc4.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# RC4 on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/Rc4/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Rc4.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_rc4_init`. -/
def init : Prog isa := scrubF 32 64 (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init)

/-- `vg_rc4_apply`. -/
def apply : Prog isa := scrubF 0 64 (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply)

end VG.Impl.Rc4.Arm.Fn
