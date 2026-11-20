module

public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Ffdh.Arm.Init

/-!
# FFDH's functions on ARMv7, as emitted

Each is its body, then its cleanup (`Impl.Scrub.Arm`): the registers a
callee may change set to constants, but the 32-bit result, and, for code
with frames, the bytes of stack its contract reserves zeroed first. The
initializations have no frames (`scrub`). A function generic over an
implementation takes its body, the code its proof is about, as an argument.
`Proof/Ffdh/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Ffdh.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ffdh_key_generation_init`. -/
def keyInit : Prog isa := scrub 32 KeyGeneration.init

/-- `vg_ffdh_parameter_generation_init`. -/
def parameterInit : Prog isa := scrub 32 Generation.init

/-- `vg_ffdh_check_domain`, of a variant's code `c`, whose frames use at
most the 128 bytes of stack its contract reserves. -/
def checkDomain (c : Prog isa) : Prog isa := scrubAll 32 128 c

/-- `vg_ffdh_check_private`, of a variant's code `c`, whose frames use at
most the 128 bytes of stack its contract reserves. -/
def checkPrivate (c : Prog isa) : Prog isa := scrubAll 32 128 c

/-- `vg_ffdh_check_public`, of the code `c` of a function generic over the
RSA Montgomery product, whose frames use at most the 176 bytes of stack its
contract reserves. -/
def checkPublic (c : Prog isa) : Prog isa := scrubAll 32 176 c

/-- `vg_ffdh_derive_public`, of its code `c`, as `checkPublic`. -/
def derivePublic (c : Prog isa) : Prog isa := scrubAll 32 176 c

/-- `vg_ffdh_exchange`, of its code `c`, as `checkPublic`. -/
def exchange (c : Prog isa) : Prog isa := scrubAll 32 176 c

/-- `vg_ffdh_generate_key_precompute`, of its code `c`, as `checkPublic`. -/
def generationPrecompute (c : Prog isa) : Prog isa := scrubAll 32 176 c

/-- `vg_ffdh_generate_key_search_cached`, of its code `c`, whose frames, and
those of the key-generation attempt it calls, use at most the 240 bytes of
stack its contract reserves. -/
def cachedKeySearch (c : Prog isa) : Prog isa := scrubAll 32 240 c

/-- `vg_ffdh_generate_parameters`, of its code `c`, whose frames, and those of
the candidate it calls, use at most the 232 bytes of stack its contract
reserves. -/
def sievedParameterSearch (c : Prog isa) : Prog isa := scrubAll 32 232 c

end VG.Impl.Ffdh.Arm.Fn
