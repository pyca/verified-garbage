module

public import VerifiedGarbage.Impl.AesSiv.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# AES-SIV on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm.lean`,
`scrubAll`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/AesSiv/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.AesSiv.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.AesSiv.Arm

/-- `vg_aes_siv_init`. -/
def init : Prog isa := scrubAll 0 2576 (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesSiv.Arm.init)

/-- `vg_aes_siv_encrypt`. -/
def encrypt : Prog isa := scrubAll 0 2624 (Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.encrypt)

/-- `vg_aes_siv_decrypt`. -/
def decrypt : Prog isa := scrubAll 32 2624 (Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.decrypt)

end VG.Impl.AesSiv.Arm.Fn
