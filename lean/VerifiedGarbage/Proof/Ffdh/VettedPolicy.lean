module

public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth

/-! Byte encoding of the reviewed public scalar-width policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.VettedPolicy
open VG

theorem bits_le_bound (a : Spec.Ffdh.Parameters) :
    Spec.Ffdh.generationScalarBits a ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) := by
  unfold Spec.Ffdh.generationScalarBits
  split
  · exact Nat.min_le_right _ _
  · exact Nat.le_refl _

theorem bits_of_unrecognized {a : Spec.Ffdh.Parameters}
    (unrecognized : Spec.Ffdh.vettedExponentBits a = none) :
    Spec.Ffdh.generationScalarBits a = Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) := by
  simp only [Spec.Ffdh.generationScalarBits, unrecognized]

/-- The whole draw keeps its original length; only its public suffix is retained. -/
def octets (a : Spec.Ffdh.Parameters) (r : List Byte) : List Byte :=
  KeyScalar.cut r (r.length - ScalarWidth.width (Spec.Ffdh.generationScalarBits a))
    (ScalarWidth.mask (Spec.Ffdh.generationScalarBits a))

theorem octets_value {a : Spec.Ffdh.Parameters} {r : List Byte}
    (nonempty : 0 < r.length)
    (fits : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) ≤ 8 * r.length) :
    Spec.Rsa.os2ip (octets a r) = Spec.Ffdh.vettedScalarOfOctets a r :=
  ScalarWidth.cut_value nonempty (Nat.le_trans (bits_le_bound a) fits)

end VG.Proof.Ffdh.VettedPolicy
