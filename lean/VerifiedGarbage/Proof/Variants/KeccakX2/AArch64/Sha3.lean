module

public import VerifiedGarbage.Proof.Sha3.AArch64.X2Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2

/-!
# With the SHA-3 extension, `vg_keccak_f1600_x2_sha3`.

The variant `VG.Variants.KeccakX2.AArch64.Sha3.variant`
(`Variants/KeccakX2/AArch64/Sha3.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.KeccakX2.AArch64.Sha3

def variant : Proof.Sha3.AArch64.X2Permutation where
  sha3 := true
  suffix := "_sha3"
  features := ["sha3"]
  code := Impl.Sha3.AArch64.Neon.X2.code true
  code_eq := rfl
  verified := Proof.Sha3.AArch64.Neon.X2.verified true

end VG.Proof.Variants.KeccakX2.AArch64.Sha3
