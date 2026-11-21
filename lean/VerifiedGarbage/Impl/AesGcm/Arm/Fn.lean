module

public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Impl.AesGcm.Arm.SealGather
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# AES-GCM on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm.lean`,
`scrubAll`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/AesGcm/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.AesGcm.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.AesGcm.Arm

/-- `vg_aes_gcm_init`. -/
def init : Prog isa := scrubAll 0 2576 (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init)

/-- `vg_aes_gcm_stream_init`. -/
def streamInit : Prog isa := scrubAll 0 2592 (Impl.StackScratch.Arm.withStackScratch 2576 0 Impl.AesGcm.Arm.streamInit)

/-- `vg_aes_gcm_stream_aad`. -/
def streamAad : Prog isa := scrubAll 0 2592 (Impl.StackScratch.Arm.withStackScratch 2576 2 Impl.AesGcm.Arm.streamAad)

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa := scrubAll 0 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamEncrypt)

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa := scrubAll 0 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamDecrypt)

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa := scrubAll 0 2608 (Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.streamFinish)

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerify : Prog isa := scrubAll 32 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamVerify)

/-- `vg_aes_gcm_seal`. -/
def «seal» : Prog isa := scrubAll 0 2608 (Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.«seal»)

/-- `vg_aes_gcm_open`. -/
def «open» : Prog isa := scrubAll 32 2608 (Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.«open»)

/-- `vg_aes_gcm_seal_gather`: the gather, then a call of `vg_aes_gcm_seal`'s
code without its cleanup, as the internal `vg_aes_gcm_seal_entry`. -/
def sealGather : Prog isa :=
  scrubAll 0 2640 (Impl.AesGcm.Arm.SealGather.sealGather "vg_aes_gcm_seal_entry"
    (Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.«seal»))

/-- `vg_aes_gcm_open_to`. -/
def openTo : Prog isa := scrubAll 32 2624 (Impl.StackScratch.Arm.withStackScratch 2608 8 Impl.AesGcm.Arm.openTo)

end VG.Impl.AesGcm.Arm.Fn
