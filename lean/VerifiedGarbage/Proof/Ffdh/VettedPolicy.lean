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

theorem bits_of_recognized {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    Spec.Ffdh.generationScalarBits a = min bits (Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a)) := by
  simp only [Spec.Ffdh.generationScalarBits, recognized]

theorem scalar_of_unrecognized {a : Spec.Ffdh.Parameters} (r : List Byte)
    (unrecognized : Spec.Ffdh.vettedExponentBits a = none) :
    Spec.Ffdh.vettedScalarOfOctets a r = Spec.Ffdh.scalarOfOctets a r := by
  rw [Spec.Ffdh.vettedScalarOfOctets, bits_of_unrecognized unrecognized]
  rfl

/-- The whole draw keeps its original length; only its public suffix is retained. -/
def octets (a : Spec.Ffdh.Parameters) (r : List Byte) : List Byte :=
  KeyScalar.cut r (r.length - ScalarWidth.width (Spec.Ffdh.generationScalarBits a))
    (ScalarWidth.mask (Spec.Ffdh.generationScalarBits a))

theorem octets_length {a : Spec.Ffdh.Parameters} {r : List Byte}
    (nonempty : 0 < r.length)
    (fits : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) ≤ 8 * r.length) :
    (octets a r).length = r.length :=
  ScalarWidth.cut_length nonempty (Nat.le_trans (bits_le_bound a) fits)

theorem octets_value {a : Spec.Ffdh.Parameters} {r : List Byte}
    (nonempty : 0 < r.length)
    (fits : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) ≤ 8 * r.length) :
    Spec.Rsa.os2ip (octets a r) = Spec.Ffdh.vettedScalarOfOctets a r :=
  ScalarWidth.cut_value nonempty (Nat.le_trans (bits_le_bound a) fits)

theorem octets_significant (a : Spec.Ffdh.Parameters) (r : List Byte) :
    Spec.Rsa.os2ip ((octets a r).drop
      (r.length - ScalarWidth.width (Spec.Ffdh.generationScalarBits a))) =
      Spec.Rsa.os2ip (octets a r) :=
  KeyScalar.os2ip_cut_drop _ _ _

end VG.Proof.Ffdh.VettedPolicy
