module

public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Sm4Gcm.Arm

/-!
# SM4-GCM on ARMv7, as emitted

Each function is its code with its working space in a frame on the stack
(`withStackScratch`, `withRegScratch`), then its cleanup
(`Impl.Scrub.Arm.scrubAll`): the stack its contract reserves zeroed, which
covers that frame and the frames of the functions it calls (`vg_ghash`,
`vg_sm4_ctr32`, `vg_sm4_expand_key_core`, internal functions whose code is
verified without a cleanup of its own), and the registers a callee may
change set to constants, but the result of `open` and `stream_verify`.
`Proof/Sm4Gcm/Arm/Scrub.lean` states that each returns without secret
residue.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.StackScratch.Arm

/-- `vg_sm4_gcm_init`. -/
def init : Prog isa := scrubAll 0 2288 (withRegScratch 768 .r2 Impl.Sm4Gcm.Arm.init)

/-- `vg_sm4_gcm_seal`. -/
def «seal» : Prog isa := scrubAll 0 2320 (withStackScratch 800 4 Impl.Sm4Gcm.Arm.«seal»)

/-- `vg_sm4_gcm_open`. -/
def «open» : Prog isa := scrubAll 32 2320 (withStackScratch 800 5 Impl.Sm4Gcm.Arm.«open»)

/-- `vg_sm4_gcm_stream_init`. -/
def streamInit : Prog isa := scrubAll 0 2304 (withStackScratch 784 0 Impl.Sm4Gcm.Arm.streamInit)

/-- `vg_sm4_gcm_stream_aad`. -/
def streamAad : Prog isa := scrubAll 0 2304 (withStackScratch 784 2 Impl.Sm4Gcm.Arm.streamAad)

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa := scrubAll 0 2320 (withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamEncrypt)

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa := scrubAll 0 2320 (withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamDecrypt)

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinish : Prog isa := scrubAll 0 2320 (withStackScratch 800 3 Impl.Sm4Gcm.Arm.streamFinish)

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerify : Prog isa := scrubAll 32 2320 (withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamVerify)

end VG.Impl.Sm4Gcm.Arm.Fn
