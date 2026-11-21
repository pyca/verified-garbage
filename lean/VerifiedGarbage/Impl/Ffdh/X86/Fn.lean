module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
public import VerifiedGarbage.Impl.Ffdh.X86.Derive
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.Impl.Ffdh.X86.ParamInit
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# FFDH on x86 (32-bit): the functions as emitted

Each function, then its cleanup: for those with frames and calls
(`Impl.Scrub.X86.scrubAll rb W`), the `W` bytes of stack below `esp` that they
use zeroed; for `vg_ffdh_key_generation_init` and
`vg_ffdh_parameter_generation_init`, which call nothing and have no frame,
none (`Impl.Scrub.X86.scrub rb`). Then the registers a callee may change are
cleared but the `rb` bits of the result, so that each returns without secret
residue.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86.Fn

open VG.X86

/-- `vg_ffdh_check_domain`, as emitted. -/
def checkDomain : Prog isa := Impl.Scrub.X86.scrubAll 32 172 Impl.Ffdh.X86.VettedValidation.code

/-- `vg_ffdh_check_public`, as emitted. -/
def checkPublic : Prog isa := Impl.Scrub.X86.scrubAll 32 172 Impl.Ffdh.X86.CheckPublic.code

/-- `vg_ffdh_check_private`, as emitted. -/
def checkPrivate : Prog isa := Impl.Scrub.X86.scrubAll 32 172 Impl.Ffdh.X86.CheckPrivate.code

/-- `vg_ffdh_exchange`, as emitted. -/
def exchange : Prog isa := Impl.Scrub.X86.scrubAll 32 172 Impl.Ffdh.X86.Exchange.code

/-- `vg_ffdh_derive_public`, as emitted. -/
def derivePublic : Prog isa := Impl.Scrub.X86.scrubAll 32 172 Impl.Ffdh.X86.DerivePublic.code

/-- `vg_ffdh_key_generation_init`, as emitted. -/
def keyInit : Prog isa := Impl.Scrub.X86.scrub 32 Impl.Ffdh.X86.KeyInit.code

/-- `vg_ffdh_generate_key_precompute`, as emitted. -/
def generationPrecompute : Prog isa := Impl.Scrub.X86.scrubAll 32 172 Impl.Ffdh.X86.Cached.Precompute.code

/-- `vg_ffdh_generate_key_search_cached`, as emitted. -/
def cachedKeySearch : Prog isa := Impl.Scrub.X86.scrubAll 32 228 Impl.Ffdh.X86.Cached.Search.code

/-- `vg_ffdh_parameter_generation_init`, as emitted. -/
def parameterInit : Prog isa := Impl.Scrub.X86.scrub 32 Impl.Ffdh.X86.ParamInit.code

/-- `vg_ffdh_generate_parameters`, as emitted. -/
def sievedParameterSearch : Prog isa := Impl.Scrub.X86.scrubAll 32 212 Impl.Ffdh.X86.ParamSearch.code

end VG.Impl.Ffdh.X86.Fn
