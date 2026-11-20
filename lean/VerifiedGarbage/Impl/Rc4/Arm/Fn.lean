module

public import VerifiedGarbage.Impl.Rc4.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.ArmSel

/-!
# RC4 on ARMv7, as emitted

Each function's code, which wipes its own working space, followed by its
cleanup (`Impl/Residue/ArmSel.lean`, `scrubSel`): of the stack its contract
reserves, where its frames were, only the words that the residue analysis
(`Arm.rtaint`) finds may differ between two runs zeroed (`…Words`, offsets in
words from the lowest address of that stack), and the registers a callee may
change, but its result, set to constants: none, so the cleanup
stores nothing on the stack.
`Proof/Rc4/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Rc4.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- The words RC4's functions leave secret: none. -/
def noWords : List Nat := []

/-- `vg_rc4_init`. -/
def init : Prog isa := scrubSel 32 64 noWords (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init)

/-- `vg_rc4_apply`. -/
def apply : Prog isa := scrubSel 0 64 noWords (Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply)

end VG.Impl.Rc4.Arm.Fn
