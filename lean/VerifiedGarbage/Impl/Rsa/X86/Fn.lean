module

public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSA's key functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubF rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Rsa.X86.Fn

open VG.X86

/-- `vg_rsa_recover_primes_det`, as emitted. -/
def recoverPrimesDet : Prog isa := Impl.Scrub.X86.scrub 32 RecoverDetRt.code

/-- `vg_rsa_check_key`, as emitted. -/
def checkKey : Prog isa := Impl.Scrub.X86.scrub 32 (KeyCheckRt.code true)

/-- `vg_rsa_crt_values`, as emitted. -/
def crtValues : Prog isa := Impl.Scrub.X86.scrubF 32 52 CrtValuesRt.code

/-- `vg_rsa_public_precompute`, as emitted. -/
def publicPrecompute : Prog isa := Impl.Scrub.X86.scrubF 32 96 Impl.Bignum.X86.PrecomputeFn.code

/-- `vg_rsa_private_precompute`, calling `vg_rsa_public_precompute`'s code as
the internal `vg_rsa_public_precompute_core`, as emitted. -/
def privatePrecompute : Prog isa :=
  Impl.Scrub.X86.scrubF 32 196
    (Impl.Bignum.X86.PrivPre.code "vg_rsa_public_precompute_core" Impl.Bignum.X86.PrecomputeFn.code
      "vg_rsa_private_precompute_primes" Impl.Bignum.X86.PrivPre.primes)

end VG.Impl.Rsa.X86.Fn
