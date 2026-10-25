module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.ResidentBackend

@[expose] public section
namespace VG.Variants.Keccak.AArch64.Lazy

def variant : Proof.Sha3.AArch64.Permutation :=
  Proof.Sha3.AArch64.Scalar.Lazy.ResidentBackend.backend

end VG.Variants.Keccak.AArch64.Lazy
