module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Framework.Omega

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
