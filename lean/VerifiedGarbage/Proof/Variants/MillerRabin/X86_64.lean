module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Adx
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Ifma

/-! # The implementations of `MillerRabin` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64 in
def adx : RoundImpl := Proof.Variants.MillerRabin.X86_64.Adx.variant

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64 in
def base : RoundImpl := Proof.Variants.MillerRabin.X86_64.Base.variant

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64 in
def ifma : RoundImpl := Proof.Variants.MillerRabin.X86_64.Ifma.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [ifma, adx, base]

end VG.Proof.Variants.MillerRabin.X86_64
