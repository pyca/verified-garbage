module

public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Ffdh.AArch64.Cached.PolicyRule`, which only this module used -/

section

/-! The native width equals the already reviewed generationScalarBits policy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG
open VG.Impl.Ffdh.AArch64.Cached

theorem recognized_nonzero {a : Spec.Ffdh.Parameters} {bits : Nat}
 (h : Spec.Ffdh.vettedExponentBits a=some bits) : bits≠0 := by
 unfold Spec.Ffdh.vettedExponentBits at h
 repeat' split at h
 all_goals cases h
 all_goals decide

theorem policyWidth_spec {k : Nat} {dom : List Byte} (positive : 0<k)
 (size : dom.length=2*k ∨ dom.length=3*k)
 (normalized : 2^(64*((k+7)/8-1))≤Spec.Rsa.os2ip (dom.take k)) :
 policyWidth (Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))) k dom Policy.groups=
 Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) := by
 rw [policyWidth_rule]
 · rw [Policy.recognize_spec positive size normalized]
   cases h : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
   | none => simp only [Option.getD_none,ite_true,Spec.Ffdh.generationScalarBits,h]
   | some bits =>
     simp only [Option.getD_some,ite_eq_right (recognized_nonzero h),Spec.Ffdh.generationScalarBits,h]
     exact Nat.min_comm _ _
 · intro g hg
   simp only [Policy.groups,List.mem_cons,List.not_mem_nil,or_false] at hg
   rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end VG.Proof.Ffdh.AArch64.Cached

end

end


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
 | none => simp only [scalarBound,q,Option.getD_none];omega_using [mod]
 | some v =>
   have bound := (facts.2.2 v q).1.2.1
   simp only [scalarBound,q,Option.getD_some]
   omega_using [bound]

theorem generation_bits_positive {k : Nat} {dom : List Byte} (valid : Spec.Ffdh.domainValid k dom=true) :
 0<generationScalarBits (domainOf k dom) := by
 have positive := scalarBound_positive valid
 have length : 0<bitLength (scalarBound (domainOf k dom)) := by
  unfold bitLength
  rw [ite_eq_right (by omega_using [positive] : scalarBound (domainOf k dom)≠0)]
  omega_using []
 unfold generationScalarBits
 cases h : Spec.Ffdh.vettedExponentBits (domainOf k dom) with
 | none => exact length
 | some bits =>
   have := recognized_nonzero h
   exact Nat.lt_min.mpr ⟨by omega_using [this],length⟩

theorem generation_bits_bound {k : Nat} {dom : List Byte} (positive : 0<k) (size : k≤1024) :
 generationScalarBits (domainOf k dom)≤8192 := by
 have := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (domainOf k dom)
 have := scalarBound_bits_fit (dom:=dom) positive
 omega_arith

theorem domain_normalized {k : Nat} {dom : List Byte} (positive : 0<k)
 (valid : Spec.Ffdh.domainValid k dom=true) :
 2^(64*((k+7)/8-1))≤(domainOf k dom).p := by
 have modulus := VG.Proof.Ffdh.domainValid_mod valid
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modulus
 have lower := modulus.2
 rw [VG.Proof.Bignum.pow256_eq] at lower
 exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) lower

end VG.Proof.Ffdh.AArch64.Cached
