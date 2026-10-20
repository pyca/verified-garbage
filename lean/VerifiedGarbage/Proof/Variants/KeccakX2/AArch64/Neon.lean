module

public import VerifiedGarbage.Proof.Sha3.AArch64.X2Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2

/-!
# The baseline AdvSIMD implementation, `vg_keccak_f1600_x2`.

The variant `VG.Variants.KeccakX2.AArch64.Neon.variant`
(`Variants/KeccakX2/AArch64/Neon.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.KeccakX2.AArch64.Neon

def variant : Proof.Sha3.AArch64.X2Permutation where
  sha3 := false
  suffix := ""
  features := []
  code := Impl.Sha3.AArch64.Neon.X2.code false
  code_eq := rfl
  verified := Proof.Sha3.AArch64.Neon.X2.verified false

end VG.Proof.Variants.KeccakX2.AArch64.Neon
