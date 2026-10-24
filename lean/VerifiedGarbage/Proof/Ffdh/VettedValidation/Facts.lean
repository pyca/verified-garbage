module

public import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Modp2048
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Ffdhe2048
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Modp3072
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Ffdhe3072
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Modp4096
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Ffdhe4096
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Modp6144
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Ffdhe6144
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Modp8192
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Ffdhe8192
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! The fixed standard groups satisfy the existing algebraic import contract. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation
open VG
open VG.Impl.Ffdh

private theorem prime_facts (g : VettedGroups.Group) (member : g∈VettedGroups.groups) :
  512≤Spec.RsaKeyGen.bitLength g.prime ∧ Spec.RsaKeyGen.bitLength g.prime≤8192 ∧
  g.prime % 2=1 ∧ 2<g.prime-1 ∧ 2<(g.prime-1)/2 ∧ ((g.prime-1)/2)%2=1 ∧
  (g.prime-1)/2<g.prime-1 ∧ (g.prime-1)%((g.prime-1)/2)=0 := by
  simp only [VettedGroups.groups,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem group_subgroup (g : VettedGroups.Group) (member : g∈VettedGroups.groups) :
  2 ^ ((g.prime-1)/2) % g.prime=1 := by
  have primes : g.prime=Spec.Ffdh.modp2048Prime ∨ g.prime=Spec.Ffdh.ffdhe2048Prime ∨ g.prime=Spec.Ffdh.modp3072Prime ∨ g.prime=Spec.Ffdh.ffdhe3072Prime ∨ g.prime=Spec.Ffdh.modp4096Prime ∨ g.prime=Spec.Ffdh.ffdhe4096Prime ∨ g.prime=Spec.Ffdh.modp6144Prime ∨ g.prime=Spec.Ffdh.ffdhe6144Prime ∨ g.prime=Spec.Ffdh.modp8192Prime ∨ g.prime=Spec.Ffdh.ffdhe8192Prime := by
    simp only [VettedGroups.groups,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  rcases primes with h|h|h|h|h|h|h|h|h|h
  · rw [h]; exact Modp2048.subgroup
  · rw [h]; exact Ffdhe2048.subgroup
  · rw [h]; exact Modp3072.subgroup
  · rw [h]; exact Ffdhe3072.subgroup
  · rw [h]; exact Modp4096.subgroup
  · rw [h]; exact Ffdhe4096.subgroup
  · rw [h]; exact Modp6144.subgroup
  · rw [h]; exact Ffdhe6144.subgroup
  · rw [h]; exact Modp8192.subgroup
  · rw [h]; exact Ffdhe8192.subgroup

theorem group_parameters_valid (g : VettedGroups.Group) (member : g∈VettedGroups.groups) (q : Option Nat)
    (order : q=none ∨ q=some ((g.prime-1)/2)) :
    Spec.Ffdh.parametersValid ⟨g.prime,2,q⟩=true := by
  obtain ⟨lo,hi,odd,gen,qlo,qodd,qhi,divides⟩ := prime_facts g member
  rcases order with rfl|rfl
  · simp only [Spec.Ffdh.parametersValid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨⟨⟨⟨⟨lo,hi⟩,odd⟩,by decide⟩,gen⟩,True.intro⟩
  · simp only [Spec.Ffdh.parametersValid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
      VG.Proof.Bignum.powMod_eq]
    exact ⟨⟨⟨⟨⟨lo,hi⟩,odd⟩,by decide⟩,gen⟩,⟨⟨⟨⟨qlo,qodd⟩,qhi⟩,divides⟩,group_subgroup g member⟩⟩

theorem matched_domain_valid {g : VettedGroups.Group} (member : g∈VettedGroups.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length=2*k ∨ dom.length=3*k)
    (matched : k=g.len ∧ dom=g.domain.take dom.length) : Spec.Ffdh.domainValid k dom=true := by
  obtain ⟨rfl,matched⟩:=matched
  have params := VG.Proof.Ffdh.VettedGroupFacts.group_parameters g member shape
  have domain := congrArg (Spec.Ffdh.domainOf g.len) matched
  rw [params] at domain
  unfold Spec.Ffdh.domainValid
  rw [domain]
  rw [Bool.and_eq_true]
  refine ⟨group_parameters_valid g member _ ?_,?_⟩
  · split <;> simp
  · exact decide_eq_true (VG.Proof.Ffdh.VettedGroupFacts.group_bounds g member).2.1

/-- Any exact-table recognition success establishes the unchanged validation predicate.
No assumption about the input modulus is needed before recognition. -/
theorem recognized_domain_valid (gs : List VettedGroups.Group)
    (members : ∀ g ∈ gs, g ∈ VettedGroups.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hit : VettedGroups.recognizeList gs k dom ≠ 0) :
    Spec.Ffdh.domainValid k dom = true := by
  induction gs with
  | nil => simp only [VettedGroups.recognizeList] at hit; exact False.elim (hit rfl)
  | cons g gs ih =>
    by_cases matched : g.len = k ∧ dom = g.domain.take dom.length
    · exact matched_domain_valid (members g (by simp)) shape ⟨matched.1.symm, matched.2⟩
    · apply ih (fun x hx => members x (by simp [hx]))
      simpa only [VettedGroups.recognizeList, ite_eq_right matched] using hit


end VG.Proof.Ffdh.VettedValidation
