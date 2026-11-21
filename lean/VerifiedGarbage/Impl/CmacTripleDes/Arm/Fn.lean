module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Streaming TDEA-CMAC on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm.lean`,
`scrubAll`): the stack its contract reserves, where its working space was,
zeroed, and the registers a callee may change set to constants.
`stream_init` keeps its working space in a frame of 640 bytes
(`withRegScratch`), `absorb` and `finish` in one of 704 and 656
(`withStackScratch`), whose contracts reserve 708 and 660 bytes: the cleanup
zeroes the next multiples of 8, 712 and 664. None returns a value.
`Proof/CmacTripleDes/Arm/Scrub.lean` states that each returns without secret
residue.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.StackScratch.Arm

/-- `vg_cmac_triple_des_stream_init`. -/
def streamInit : Prog isa := scrubAll 0 640 (withRegScratch 640 .r3 Impl.CmacTripleDes.Stream.Arm.streamInit)

/-- `vg_cmac_triple_des_absorb`. -/
def absorb : Prog isa := scrubAll 0 712 (withStackScratch 704 2 Impl.CmacTripleDes.Stream.Arm.absorb)

/-- `vg_cmac_triple_des_finish`. -/
def finish : Prog isa := scrubAll 0 664 (withStackScratch 656 1 Impl.CmacTripleDes.Stream.Arm.finish)

end VG.Impl.CmacTripleDes.Arm.Fn
