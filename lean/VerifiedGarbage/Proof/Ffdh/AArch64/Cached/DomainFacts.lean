module

public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRule
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! Public geometry and scalar-width bounds for every accepted domain. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG
open VG.Spec.Ffdh (domainOf scalarBound generationScalarBits)
open VG.Spec.RsaKeyGen (bitLength)

theorem scalarBound_bits_fit {k : Nat} {dom : List Byte} (positive : 0<k) :
 bitLength (scalarBound (domainOf k dom))≤8*k := by
 have bound : scalarBound (domainOf k dom)<2^(8*k) := by
  unfold scalarBound domainOf
  split
  · simp only [Option.getD_some]
    have h := VG.Proof.Bignum.os2ip_lt ((dom.drop (2*k)).take k)
    have len := List.length_take_le k (dom.drop (2*k))
    rw [VG.Proof.Bignum.pow256_eq] at h
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
  · simp only [Option.getD_none]
    have h := VG.Proof.Bignum.os2ip_lt (dom.take k)
    have len := List.length_take_le k dom
    rw [VG.Proof.Bignum.pow256_eq] at h
    have cap := Nat.pow_le_pow_right (n:=2) (by decide) (show 8*(dom.take k).length≤8*k by omega)
    omega
 unfold bitLength
 split
 · omega
 · have := (Nat.log2_lt (by assumption)).mpr bound
   omega

theorem scalarBound_positive {k : Nat} {dom : List Byte} (valid : Spec.Ffdh.domainValid k dom=true) :
 0<scalarBound (domainOf k dom) := by
 have facts := (VG.Proof.Ffdh.domainValid_iff k dom).mp valid
 have mod := facts.1
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at mod
 cases q : (domainOf k dom).q with
 | none => simp only [scalarBound,q,Option.getD_none];omega
 | some v =>
   have bound := (facts.2.2 v q).1.2.1
   simp only [scalarBound,q,Option.getD_some]
   omega

theorem generation_bits_positive {k : Nat} {dom : List Byte} (valid : Spec.Ffdh.domainValid k dom=true) :
 0<generationScalarBits (domainOf k dom) := by
 have positive := scalarBound_positive valid
 have length : 0<bitLength (scalarBound (domainOf k dom)) := by
  unfold bitLength
  rw [ite_eq_right (by omega : scalarBound (domainOf k dom)≠0)]
  omega
 unfold generationScalarBits
 cases h : Spec.Ffdh.vettedExponentBits (domainOf k dom) with
 | none => exact length
 | some bits =>
   have := recognized_nonzero h
   exact Nat.lt_min.mpr ⟨by omega,length⟩

theorem generation_bits_bound {k : Nat} {dom : List Byte} (positive : 0<k) (size : k≤1024) :
 generationScalarBits (domainOf k dom)≤8192 := by
 have := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (domainOf k dom)
 have := scalarBound_bits_fit (dom:=dom) positive
 omega

theorem domain_normalized {k : Nat} {dom : List Byte} (positive : 0<k)
 (valid : Spec.Ffdh.domainValid k dom=true) :
 2^(64*((k+7)/8-1))≤(domainOf k dom).p := by
 have modulus := VG.Proof.Ffdh.domainValid_mod valid
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modulus
 have lower := modulus.2
 rw [VG.Proof.Bignum.pow256_eq] at lower
 exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) lower

end VG.Proof.Ffdh.AArch64.Cached
