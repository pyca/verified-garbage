module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Adx
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Base

/-! # The implementations of `DsaArithmetic` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 in
def adx : Backend := Proof.Variants.DsaArithmetic.X86_64.Adx.variant

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 in
def base : Backend := Proof.Variants.DsaArithmetic.X86_64.Base.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [adx, base]

end VG.Proof.Variants.DsaArithmetic.X86_64
