module
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Witness-sampler equations for a full-width big-endian draw -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem sample_spec_good {bs : List Byte} {m : Nat}
    (bits : Spec.RsaKeyGen.bitLength (m - 1) = 8 * bs.length)
    (good : 2 ≤ Spec.Dsa.decodeBE bs ∧ Spec.Dsa.decodeBE bs < m - 1) :
    Spec.RsaKeyGen.witness (m - 1) (Spec.Dsa.decodeBE bs) = (Spec.Dsa.decodeBE bs, true) := by
  have fit : Spec.Dsa.decodeBE bs < 2 ^ (8 * bs.length) := by
    rw [← VG.Proof.Bignum.pow256_eq]
    exact VG.Proof.Dsa.decodeBE_lt bs
  rw [Spec.RsaKeyGen.witness, bits, Nat.mod_eq_of_lt fit, ite_eq_left good]

theorem sample_spec_bad {bs : List Byte} {m : Nat} (len : 2 ≤ bs.length)
    (bits : Spec.RsaKeyGen.bitLength (m - 1) = 8 * bs.length)
    (bad : ¬ (2 ≤ Spec.Dsa.decodeBE bs ∧ Spec.Dsa.decodeBE bs < m - 1)) :
    Spec.RsaKeyGen.witness (m - 1) (Spec.Dsa.decodeBE bs) =
      (Spec.Dsa.decodeBE (VG.Proof.Dsa.Generation.forcedWitnessBytes bs), false) :=
  VG.Proof.Dsa.Generation.forcedWitnessBytes_spec len bits bad
end VG.Proof.Dsa.X86.Generation
