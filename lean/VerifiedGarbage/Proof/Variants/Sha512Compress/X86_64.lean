module

public import VerifiedGarbage.Proof.Sha512.X86_64.Variant

/-! # The implementations of `Sha512Compress` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Sha512Compress.X86_64

def shaNi : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.shani

def avx2 : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.avx2

def scalar : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Proof.Sha512.X86_64.Compress := [shaNi, avx2, scalar]

end VG.Proof.Variants.Sha512Compress.X86_64
