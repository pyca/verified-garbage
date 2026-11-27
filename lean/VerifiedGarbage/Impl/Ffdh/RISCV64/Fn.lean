module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.CachedSearch
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public import VerifiedGarbage.Impl.Ffdh.RISCV64.CheckPrivate
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Derive
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Domain
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Init
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Search
public import VerifiedGarbage.Impl.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Impl.Ffdh.RISCV64.ParameterCandidate
public import VerifiedGarbage.Impl.Ffdh.RISCV64.VettedValidation
public import VerifiedGarbage.Impl.Ffdh.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# FFDH on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`):
the caller-saved registers cleared but the 32 bits of its result, and the
stack its frames use zeroed (64 bytes for the key search, 128 for the
parameter search, none for the others), so that it returns without secret
residue.

The parameter search, `vg_ffdh_generate_parameters`, is given the code of a
Miller–Rabin round's implementation (`round`, named with `suffix`), which its
candidate test calls.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_ffdh_parameter_generation_init`. -/
def parameterInit : Prog isa := scrubAll 32 0 Generation.init

/-- `vg_ffdh_key_generation_init`. -/
def keyInit : Prog isa := scrubAll 32 0 KeyGeneration.init

/-- `vg_ffdh_check_public`. -/
def checkPublic : Prog isa := scrubAll 32 0 Domain.checkPublic

/-- `vg_ffdh_check_domain`. -/
def checkDomain : Prog isa := scrubAll 32 0 VettedValidation.code

/-- `vg_ffdh_exchange`. -/
def exchange : Prog isa := scrubAll 32 0 RISCV64.exchange

/-- `vg_ffdh_derive_public`. -/
def derivePublic : Prog isa := scrubAll 32 0 Derive.derivePublic

/-- `vg_ffdh_check_private`. -/
def checkPrivate : Prog isa := scrubAll 32 0 CheckPrivate.checkPrivate

/-- `vg_ffdh_generate_key_precompute`. -/
def precompute : Prog isa := scrubAll 32 0 Cached.Precompute.code

/-- The key search, calling `vg_ffdh_generate_key_cached`. -/
def cachedKeySearchBody : Prog isa :=
  Cached.Search.code (.call "vg_ffdh_generate_key_cached" Cached.Generate.code)

/-- `vg_ffdh_generate_key_search_cached`. -/
def cachedKeySearch : Prog isa := scrubAll 32 64 cachedKeySearchBody

/-- The parameter search with the round `round`, calling
`vg_ffdh_parameter_candidate_sieved`. -/
def sievedParameterSearchBody (suffix : String) (round : Prog isa) : Prog isa :=
  Generation.Search.code (.call ("vg_ffdh_parameter_candidate_sieved" ++ suffix)
    (ParameterCandidate.code ("vg_miller_rabin_round" ++ suffix) round))

/-- `vg_ffdh_generate_parameters`. -/
def sievedParameterSearch (suffix : String) (round : Prog isa) : Prog isa :=
  scrubAll 32 128 (sievedParameterSearchBody suffix round)

end VG.Impl.Ffdh.RISCV64.Fn
