module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Impl.Ffdh.AArch64.Derive
public import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowCall
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-!
# FFDH on AArch64, as emitted

Each function with the functions it calls and its cleanup
(`Impl.Scrub.AArch64.scrubOf`: the registers its code may write cleared,
and the stack it uses zeroed), so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.Fn

open VG VG.AArch64 VG.Impl.Scrub.AArch64

/-- The selection from a window of 32 powers, with vector instructions when
the modulus is whole 64-byte blocks (RSA's). -/
def select : Prog isa :=
  Impl.Rsa.AArch64.WindowSelectVector.select 32 (Impl.Bignum.AArch64.seqs Impl.Rsa.AArch64.WindowFive.tabSelect32)

/-- A window of the exponentiation: a call of RSA's
`vg_rsa_square_window5`. -/
def window : Prog isa :=
  Impl.Rsa.AArch64.WindowCall.call "vg_rsa_square_window5"
    (Impl.Rsa.AArch64.WindowShared.code
      (Impl.Rsa.AArch64.WindowFive.windowBody Impl.Bignum.AArch64.ProductDispatch.mm select))

/-- `vg_ffdh_generate_key_precompute`. -/
def precompute : Prog isa :=
  scrubOf 0 32 (Cached.Precompute.code Impl.Bignum.AArch64.ProductDispatch.mm)

/-- `vg_ffdh_generate_key_search_cached`, calling
`vg_ffdh_generate_key_cached`. -/
def cachedKeySearch : Prog isa :=
  scrubOf 64 32 (Cached.Search.code
    (.call "vg_ffdh_generate_key_cached" (Cached.Generate.code Impl.Bignum.AArch64.ProductDispatch.mm)))

/-- `vg_ffdh_check_public`. -/
def checkPublic : Prog isa :=
  scrubOf 0 32 (Domain.CheckPublic.code window select Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_ffdh_check_domain`. -/
def checkDomain : Prog isa :=
  scrubOf 0 32 (VettedValidation.code window select Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_ffdh_exchange`. -/
def exchange : Prog isa :=
  scrubOf 0 32 (Domain.Exchange.code window select Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_ffdh_check_private`. -/
def checkPrivate : Prog isa :=
  scrubOf 0 32 (Domain.CheckPrivate.code window select Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_ffdh_derive_public`. -/
def derivePublic : Prog isa :=
  scrubOf 0 32 (Domain.DerivePublic.code window select Impl.Bignum.AArch64.SquareEightCall.mm)

/-- `vg_ffdh_parameter_candidate_sieved`: its own arithmetic with the
multiplication `mm`, calling the shared round `vg_miller_rabin_round`, whose
multiplication is `rmm`. -/
def parameterCandidate (suffix : String) (mm rmm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  ParameterCandidate.code mm
    [Impl.MillerRabin.AArch64.Caller.call ("vg_miller_rabin_round" ++ suffix) (Impl.MillerRabin.AArch64.round rmm)]

/-- `vg_ffdh_generate_parameters`'s search, calling
`vg_ffdh_parameter_candidate_sieved`. -/
def parameterSearch (suffix : String) (mm rmm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubOf 32 32 (Generation.Search.code
    (.call ("vg_ffdh_parameter_candidate_sieved" ++ suffix) (parameterCandidate suffix mm rmm)))

end VG.Impl.Ffdh.AArch64.Fn
