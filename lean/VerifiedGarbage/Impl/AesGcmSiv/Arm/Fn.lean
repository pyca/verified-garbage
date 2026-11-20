module

public import VerifiedGarbage.Impl.AesGcmSiv.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# AES-GCM-SIV on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/AesGcmSiv/Arm/Verified.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.AesGcmSiv.Arm

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa := scrubF 0 3808 (Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«seal»)

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa := scrubF 32 3808 (Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«open»)

end VG.Impl.AesGcmSiv.Arm.Fn
