module

public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend
public import VerifiedGarbage.Proof.Sha512.AArch64.ScalarBackend

/-! # The implementations of `Sha512Compress` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sha512Compress.AArch64

def sha3 : Proof.Sha512.AArch64.Compress := Proof.Sha512.AArch64.Sha3.backend

def scalar : Proof.Sha512.AArch64.Compress := Proof.Sha512.AArch64.Scalar.backend

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Proof.Sha512.AArch64.Compress := [sha3, scalar]

end VG.Proof.Variants.Sha512Compress.AArch64
