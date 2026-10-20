module

public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! Unrecognized groups retain the original bound-derived byte geometry. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG
open VG.Spec.RsaKeyGen (bitLength)

private theorem byte_bitLength {n : Nat} (small : n < 256) : bitLength n ≤ 8 := by
  by_cases zero : n = 0
  · simp only [zero, bitLength, ite_true]; omega
  have lower := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds zero).1
  by_contra high
  have bound : 256 ≤ 2 ^ (bitLength n - 1) :=
    Nat.pow_le_pow_right (n := 2) (by decide) (show 8 ≤ bitLength n - 1 by omega)
  omega

private theorem byte_bitLength_zero {n : Nat} (zero : bitLength n = 0) : n = 0 := by
  unfold bitLength at zero
  split at zero
  · assumption
  · omega

theorem standard_policy_geometry (p : Inputs) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    VG.Proof.Ffdh.ScalarWidth.width (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom))) = p.scalarWidth ∧
    (VG.Proof.Ffdh.ScalarWidth.mask (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom)))).setWidth 32 = p.scalarMask := by
  let head := p.boundOctets.getD p.scalarLead 0
  have headSmall : head.toNat < 256 := head.isLt
  have lead := p.scalarLeadBound
  have nonempty : p.boundOctets ≠ [] := by
    intro empty
    have len := p.boundOctetsLength
    rw [empty] at len
    have := p.minLength
    simp only [List.length_nil] at len
    omega
  have index : p.boundOctets.getD p.scalarLead 0 = p.boundOctets[p.scalarLead]'(by rw [p.boundOctetsLength]; exact lead) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [p.boundOctetsLength]; exact lead), Option.getD_some]
  have bits := VG.Proof.Ffdh.KeyScalar.bound_bits (by have := p.minLength; omega : 1 ≤ p.k)
    p.domainLengths (fun _ => ⟨odd, large⟩)
  have bitsEq : bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom)) =
      8 * (p.scalarWidth - 1) + bitLength head.toNat := by
    change _ = 8 * (p.scalarWidth - 1) + bitLength (p.boundOctets.getD p.scalarLead 0).toNat
    rw [index]
    exact bits
  have last (zero : bitLength head.toNat = 0) : p.scalarWidth = 1 := by
    have hz : head = 0 := BitVec.eq_of_toNat_eq (by change head.toNat = 0; exact byte_bitLength_zero zero)
    have stop : ¬ p.scalarLead + 1 < p.k := by
      intro more
      have nz := VG.Proof.Ffdh.lead_nonzero nonempty (by simpa only [Inputs.scalarLead, p.boundOctetsLength] using more)
      apply nz
      change p.boundOctets[p.scalarLead]'(by rw [p.boundOctetsLength]; exact lead) = 0
      rw [← index]
      exact hz
    unfold Inputs.scalarWidth
    omega
  have widthEq : VG.Proof.Ffdh.ScalarWidth.width
      (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom))) = p.scalarWidth := by
    have small := byte_bitLength headSmall
    have widths := p.scalarWidthBounds
    have zero := last
    rw [bitsEq]
    unfold VG.Proof.Ffdh.ScalarWidth.width
    omega
  refine ⟨widthEq, ?_⟩
  have headEq : VG.Proof.Ffdh.ScalarWidth.headBits
      (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom))) = bitLength head.toNat := by
    unfold VG.Proof.Ffdh.ScalarWidth.headBits
    rw [widthEq, bitsEq]
    omega
  apply BitVec.eq_of_toNat_eq
  change ((VG.Proof.Ffdh.ScalarWidth.mask _).setWidth 32).toNat =
    (BitVec.ofNat 32 (VG.Proof.Ffdh.KeyScalar.smearN head.toNat)).toNat
  rw [BitVec.toNat_setWidth, VG.Proof.Ffdh.ScalarWidth.mask_toNat, headEq,
    VG.Proof.Ffdh.KeyScalar.smearN_eq _ headSmall, BitVec.toNat_ofNat]

theorem vetted_layout_unrecognized {p : Inputs}
    (unrecognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = none)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    (ScalarLayout.vetted p).width = p.scalarWidth ∧ (ScalarLayout.vetted p).mask = p.scalarMask := by
  have geometry := standard_policy_geometry p large odd
  have fits := p.scalarWidthBounds.2
  simp only [ScalarLayout.vetted, VG.Proof.Ffdh.VettedPolicy.bits_of_unrecognized unrecognized]
  constructor
  · unfold ScalarLayout.width
    dsimp
    rw [geometry.1]
    omega
  · exact geometry.2

end VG.Proof.Ffdh.Arm
