module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.ResidentBackend

@[expose] public section

namespace VG.Variants.Keccak.AArch64.Sha3

-- FEAT_SHA3's Keccak is faster on Apple's cores, and slower on Neoverse N2.
def variant : Proof.Sha3.AArch64.Permutation :=
  { Proof.Sha3.AArch64.Sha3.ResidentBackend.backend with vendor := some "apple" }

end VG.Variants.Keccak.AArch64.Sha3
