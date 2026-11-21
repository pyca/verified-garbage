module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Impl.Ffdh.X86_64.DerivePublic
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation

/-! # FFDH on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and the `n` bytes of stack its frames use zeroed.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.Bignum.X86_64 (R2Words.choice)

/-- `Spec.Ffdh.parameterInitApi`'s function as emitted. -/
def parameterInit : Prog isa := scrubAll .sse 32 0 Generation.init

/-- `Spec.Ffdh.keyInitApi`'s function as emitted. -/
def keyInit : Prog isa := scrubAll .sse 32 0 KeyGeneration.init

/-- `Spec.Ffdh.generationPrecomputeApi`'s function as emitted, over the
Montgomery multiplication `mul`, its cleanup at the level `v`. -/
def generationPrecompute (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll v 32 8 (Cached.Precompute.code mul (.seq (.block Domain.r2Head) (R2Words.choice mul)))

/-- `Spec.Ffdh.cachedKeySearchApi`'s function as emitted, over the
Montgomery multiplication `mul`, calling its attempt as `name`. -/
def cachedKeySearch (v : VecLevel) (name : String) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll v 32 72
    (Cached.Search.code (.call name (Cached.Generate.code mul (.seq (.block Domain.r2Head) (R2Words.choice mul)))))

/-- `Spec.Ffdh.sievedParameterSearchApi`'s function as emitted, over the
Montgomery multiplication `mul` and the Miller–Rabin round `round` named
`roundName`. -/
def sievedParameterSearch (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) (roundName : String)
    (round : Prog isa) : Prog isa :=
  scrubAll v 32 160
    (Generation.Search.code (ParameterCandidate.code mul (R2Words.choice mul) (VG.Impl.MillerRabin.X86_64.Caller.call roundName round)))

/-- The domain operations' `R² mod p` over the multiplication `mul`. -/
def r2 (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (.block Domain.r2Head) (R2Words.choice mul)

/-- `Spec.Ffdh.checkPublicApi`'s function as emitted, over the Montgomery
multiplication `mul` and the exponentiation `ex`, its cleanup at the level
`v`. -/
def checkPublic (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  scrubAll v 32 8 (Domain.CheckPublic.code mul ex (r2 mul))

/-- `Spec.Ffdh.exchangeApi`'s function as emitted, over the Montgomery
multiplication `mul` and the exponentiation `ex`, its cleanup at the level
`v`. -/
def exchange (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  scrubAll v 32 8 (Domain.Exchange.code mul ex (r2 mul))

/-- `Spec.Ffdh.checkPrivateApi`'s function as emitted, over the Montgomery
multiplication `mul` and the exponentiation `ex`, its cleanup at the level
`v`. -/
def checkPrivate (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  scrubAll v 32 8 (Domain.CheckPrivate.code mul ex (r2 mul))

/-- `Spec.Ffdh.derivePublicApi`'s function as emitted, over the Montgomery
multiplication `mul` and the exponentiation `ex`, its cleanup at the level
`v`. -/
def derivePublic (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  scrubAll v 32 8 (Domain.DerivePublic.code mul ex (r2 mul))

/-- `Spec.Ffdh.checkDomainApi`'s function as emitted, over the Montgomery
multiplication `mul` and the exponentiation `ex`, its cleanup at the level
`v`. -/
def checkDomain (v : VecLevel) (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  scrubAll v 32 8 (VettedValidation.code (Domain.CheckDomain.code mul ex (r2 mul)))

end VG.Impl.Ffdh.X86_64.Fn
