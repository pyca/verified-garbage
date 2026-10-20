module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Bignum.Octets

/-! The reviewed vetted policy applied to native domain and entropy buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem Inputs.scalarBound_bits_fit (p : Inputs) :
    Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom)) ≤ 8 * p.k := by
  have bound : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) < 2 ^ (8 * p.k) := by
    unfold Spec.Ffdh.scalarBound Spec.Ffdh.domainOf
    split
    · simp only [Option.getD_some]
      have h := VG.Proof.Bignum.os2ip_lt ((p.dom.drop (2 * p.k)).take p.k)
      have size : ((p.dom.drop (2 * p.k)).take p.k).length ≤ p.k := List.length_take_le _ _
      rw [VG.Proof.Bignum.pow256_eq] at h
      exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
    · simp only [Option.getD_none]
      have h := VG.Proof.Bignum.os2ip_lt (p.dom.take p.k)
      rw [p.pLength, VG.Proof.Bignum.pow256_eq] at h
      omega
  unfold Spec.RsaKeyGen.bitLength
  split
  · omega
  · have h := (Nat.log2_lt (by assumption)).mpr bound
    omega

def vettedScalarOctets (p : Inputs) (rb : List Byte) : List Byte :=
  VG.Proof.Ffdh.VettedPolicy.octets (Spec.Ffdh.domainOf p.k p.dom) rb

theorem vettedScalarOctets_length {p : Inputs} {rb : List Byte} (size : rb.length = p.k) :
    (vettedScalarOctets p rb).length = p.k := by
  rw [← size]
  exact VG.Proof.Ffdh.VettedPolicy.octets_length (by have := p.minLength; omega)
    (by rw [size]; exact p.scalarBound_bits_fit)

theorem vettedScalarOctets_value {p : Inputs} {rb : List Byte} (size : rb.length = p.k) :
    Spec.Rsa.os2ip (vettedScalarOctets p rb) =
      Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb :=
  VG.Proof.Ffdh.VettedPolicy.octets_value (by have := p.minLength; omega)
    (by rw [size]; exact p.scalarBound_bits_fit)

end VG.Proof.Ffdh.Arm
