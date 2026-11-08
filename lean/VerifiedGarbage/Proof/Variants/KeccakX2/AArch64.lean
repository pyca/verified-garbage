module

public import VerifiedGarbage.Proof.Variants.KeccakX2.AArch64.Neon
public import VerifiedGarbage.Proof.Variants.KeccakX2.AArch64.Sha3

/-! # The implementations of `KeccakX2` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.KeccakX2.AArch64

def neon : Proof.Sha3.AArch64.X2Permutation := Proof.Variants.KeccakX2.AArch64.Neon.variant

def sha3 : Proof.Sha3.AArch64.X2Permutation := Proof.Variants.KeccakX2.AArch64.Sha3.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [sha3, neon]

end VG.Proof.Variants.KeccakX2.AArch64
