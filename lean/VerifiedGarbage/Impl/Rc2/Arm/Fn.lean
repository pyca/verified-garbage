module

public import VerifiedGarbage.Impl.Rc2.Arm.Stream
public import VerifiedGarbage.Impl.Rc2.Arm.Cbc
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm.Sel

/-!
# RC2 on ARMv7, as emitted

Each function's code, which wipes its own working space, followed by its
cleanup (`Impl/Scrub/Arm/Sel.lean`, `scrubSel`): of the stack its contract
reserves, where its frames were, only the words that the residue analysis
(`Arm.rtaint`) finds may differ between two runs zeroed (`…Words`, offsets in
words from the lowest address of that stack), and the registers a callee may
change, but its result, set to constants.
`Proof/Rc2/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Rc2.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- The words the CBC key setup leaves secret. -/
def initWords : List Nat := List.range' 0 6

/-- The words CBC encryption and decryption leave secret. -/
def cbcWords : List Nat := List.range' 0 2 ++ List.range' 130 2

/-- `vg_rc2_cbc_init`. -/
def cbcInit : Prog isa := scrubSel 32 600 initWords (Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init)

/-- `vg_rc2_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubSel 0 528 cbcWords (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt)

/-- `vg_rc2_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubSel 0 528 cbcWords (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt)

end VG.Impl.Rc2.Arm.Fn
