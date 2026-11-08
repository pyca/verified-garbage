module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Adx
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Base
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Ifma

/-! # The implementations of `RsaPrivateCrt` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86_64

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 in
def adx : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Adx.variant

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 in
def base : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Base.variant

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 in
def ifma : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Ifma.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [adx, base, ifma]

end VG.Proof.Variants.RsaPrivateCrt.X86_64
