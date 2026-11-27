module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-! # The implementations of `Sha1Compress` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sha1Compress.AArch64

def sha2 : Proof.Sha1.AArch64.Compress := Proof.Sha1.AArch64.Sha2.backend

def scalar : Proof.Sha1.AArch64.Compress := Proof.Sha1.AArch64.Scalar.backend

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Proof.Sha1.AArch64.Compress := [sha2, scalar]

end VG.Proof.Variants.Sha1Compress.AArch64
