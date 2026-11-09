module

public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2Backend
public import VerifiedGarbage.Proof.Sha256.AArch64.ScalarBackend

/-! # The implementations of `Sha256Compress` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sha256Compress.AArch64

def sha2 : Proof.Sha256.AArch64.Compress := Proof.Sha256.AArch64.Sha2.backend

def scalar : Proof.Sha256.AArch64.Compress := Proof.Sha256.AArch64.Scalar.backend

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Proof.Sha256.AArch64.Compress := [sha2, scalar]

end VG.Proof.Variants.Sha256Compress.AArch64
