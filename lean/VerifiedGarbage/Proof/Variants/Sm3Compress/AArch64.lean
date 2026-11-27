module

public import VerifiedGarbage.Proof.Sm3.AArch64.ScalarBackend

/-! # The implementations of `Sm3Compress` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.Sm3Compress.AArch64

def sm4 : Proof.Sm3.AArch64.Compress := Proof.Sm3.AArch64.Sm4.backend

def scalar : Proof.Sm3.AArch64.Compress := Proof.Sm3.AArch64.Scalar.backend

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Proof.Sm3.AArch64.Compress := [sm4, scalar]

end VG.Proof.Variants.Sm3Compress.AArch64
