module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnAdx
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx

/-! # RSA's key functions on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and the `n` bytes of stack its frames use zeroed.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)
open VG.Impl.Bignum.X86_64

/-- Montgomery multiplication as a call of `vg_rsa_mont_mul`. -/
abbrev mmBase : Nat → Nat → Nat → Prog isa := MontFn.call "vg_rsa_mont_mul" MontFn.mulBase

/-- Montgomery multiplication as a call of `vg_rsa_mont_mul_adx`. -/
abbrev mmAdx : Nat → Nat → Nat → Prog isa := MontFn.call "vg_rsa_mont_mul_adx" MontFn.mulAdx

/-- `Spec.Rsa.publicPrecomputeApi`'s function as emitted. -/
def publicPrecompute : Prog isa := scrubAll .sse 32 8 (Precompute.code mmBase)

/-- `Spec.Rsa.publicPrecomputeApi`'s function with ADX as emitted. -/
def publicPrecomputeAdx : Prog isa := scrubAll .sse 32 8 (Precompute.code mmAdx (R2Adx.choice mmAdx))

/-- `Spec.Rsa.privatePrecomputeApi`'s function as emitted. -/
def privatePrecompute : Prog isa := scrubAll .sse 32 8 (PrivPre.code mmBase)

/-- `Spec.Rsa.privatePrecomputeApi`'s function with ADX as emitted. -/
def privatePrecomputeAdx : Prog isa := scrubAll .sse 32 8 (PrivPre.code mmAdx)

/-- `Spec.Rsa.crtValuesApi`'s function as emitted. -/
def crtValues : Prog isa := scrubAll .sse 32 0 Keys.CrtValues.code

/-- `Spec.Rsa.recoverPrimesDetApi`'s function as emitted. -/
def recoverPrimesDet : Prog isa := scrubAll .sse 32 0 Keys.RecoverDet.code

/-- `Spec.Rsa.checkKeyApi`'s function as emitted. -/
def checkKey : Prog isa := scrubAll .sse 32 0 CheckKey.code

end VG.Impl.Rsa.X86_64.Fn
