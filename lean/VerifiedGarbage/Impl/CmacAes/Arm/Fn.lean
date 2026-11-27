module

public import VerifiedGarbage.Impl.CmacAes.Stream.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Streaming AES-CMAC on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm.lean`,
`scrubAll`): the stack its contract reserves, where its working space and the
frames of the functions it calls were, zeroed, and the registers a callee
may change set to constants. `init` keeps its working space in a frame of
2304 bytes (`withRegScratch`), `absorb` and `finish` in one of 2320
(`withStackScratch`). None returns a value. `Proof/CmacAes/Arm/Scrub.lean`
states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.CmacAes.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.StackScratch.Arm

/-- `vg_cmac_aes_init`. -/
def init : Prog isa := scrubAll 0 2320 (withRegScratch 2304 .r3 Impl.CmacAes.Stream.Arm.init)

/-- `vg_cmac_aes_absorb`. -/
def absorb : Prog isa := scrubAll 0 2336 (withStackScratch 2320 2 Impl.CmacAes.Stream.Arm.absorb)

/-- `vg_cmac_aes_finish`. -/
def finish : Prog isa := scrubAll 0 2336 (withStackScratch 2320 1 Impl.CmacAes.Stream.Arm.finish)

end VG.Impl.CmacAes.Arm.Fn
