module

public import VerifiedGarbage.Impl.AesOcb.Arm
public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# AES-OCB on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/AesOcb/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.AesOcb.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.AesOcb.Arm

/-- `vg_aes_ocb_init`. -/
def init : Prog isa := scrubF 0 2576 (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init)

/-- `vg_aes_ocb_seal`. -/
def «seal» : Prog isa := scrubF 0 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«seal»)

/-- `vg_aes_ocb_open`. -/
def «open» : Prog isa := scrubF 32 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«open»)

end VG.Impl.AesOcb.Arm.Fn
