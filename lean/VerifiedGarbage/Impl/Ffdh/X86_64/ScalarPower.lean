module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Fn
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFn

/-! # Sharing scalar FFDH exponentiation within the existing stack budget

The baseline arithmetic and exponentiation have no calls. Their common
power, after the caller loads the base, is shared by private-key import,
public-key derivation, and exchange. Its single call fits the existing
8-byte stack bound. Backends whose power already calls helpers retain
those calls rather than nesting another one below them.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ScalarPower

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Domain

/-- The existing scalar multiplication, inlined as in the baseline backend. -/
def mul (o a b : Nat) : Prog isa :=
  .seq (.block (MontFn.args o a b)) MontFn.mulBase

def exp : Nat → Nat → List (Prog isa) := Crt.expLoop mul Crt.tabSelect

/-- Keep the initial base load at the caller; share the rest of the power. -/
def core : Prog isa :=
  seqs ((pow mul exp sG sK sX sXl).drop (Crt.loadArr aXm sG sK).length)

def call : Option (List (Prog isa)) := some [.call "vg_ffdh_pow_shared" core]

def privateCode : Prog isa := CheckPrivate.code mul exp (Fn.r2 mul) call

def deriveCode : Prog isa := DerivePublic.code mul exp (Fn.r2 mul) call

def exchangeCode : Prog isa := Exchange.code mul exp (Fn.r2 mul) call

end VG.Impl.Ffdh.X86_64.ScalarPower

namespace VG.Impl.Ffdh.X86_64.Fn

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- Scalar private-key import with its common power shared. -/
def checkPrivateScalar : Prog isa := scrubAll .sse 32 8 ScalarPower.privateCode

/-- Scalar public-key derivation with its common power shared. -/
def derivePublicScalar : Prog isa := scrubAll .sse 32 8 ScalarPower.deriveCode

/-- Scalar exchange with its common power shared. -/
def exchangeScalar : Prog isa := scrubAll .sse 32 8 ScalarPower.exchangeCode

end VG.Impl.Ffdh.X86_64.Fn
