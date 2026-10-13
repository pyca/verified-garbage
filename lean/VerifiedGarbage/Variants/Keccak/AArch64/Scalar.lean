module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ResidentBackend

@[expose] public section

namespace VG.Variants.Keccak.AArch64.Scalar

def variant : Proof.Sha3.AArch64.Permutation := Proof.Sha3.AArch64.Scalar.ResidentBackend.backend

end VG.Variants.Keccak.AArch64.Scalar
