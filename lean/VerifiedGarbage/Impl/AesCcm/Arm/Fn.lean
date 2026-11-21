module

public import VerifiedGarbage.Impl.AesCcm.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# AES-CCM on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm.lean`,
`scrubAll`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/AesCcm/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.AesCcm.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.AesCcm.Arm

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa := scrubAll 0 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«seal»)

/-- `vg_aes_ccm_open`. -/
def «open» : Prog isa := scrubAll 32 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«open»)

end VG.Impl.AesCcm.Arm.Fn
