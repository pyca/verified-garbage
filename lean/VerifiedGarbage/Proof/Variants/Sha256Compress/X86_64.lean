module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256

/-! # The implementations of `Sha256Compress` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Sha256Compress.X86_64

def shaNi : Proof.Sha256.X86_64.Compress := Proof.Variants.MdHash.X86_64.Sha256ShaNi.compress

def avx2 : Proof.Sha256.X86_64.Compress := Proof.Variants.MdHash.X86_64.Sha256Avx2.compress

def scalar : Proof.Sha256.X86_64.Compress := Proof.Variants.MdHash.X86_64.Sha256.compress

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Proof.Sha256.X86_64.Compress := [shaNi, avx2, scalar]

end VG.Proof.Variants.Sha256Compress.X86_64
