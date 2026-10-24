module

public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets

/-! Canonical byte comparisons recognizeList exactly the reviewed group policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.VettedGroupFacts
open VG
open VG.Spec.Rsa (os2ip i2osp)
open VG.Impl.Ffdh.VettedGroups (Group groups recognizeList)

private theorem pow_chunks (n : Nat) :
    (256 : Nat) ^ n = (256 ^ 128) ^ (n / 128) * 256 ^ (n % 128) := by
  rw [← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  omega

theorem group_bounds (g : Group) (member : g ∈ groups) :
    0 < g.len ∧ 256 ^ (g.len - 1) ≤ g.prime ∧ g.prime < 256 ^ g.len := by
  rw [pow_chunks (g.len - 1), pow_chunks g.len]
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem group_aligned (g : Group) (member : g ∈ groups) : g.len % 8 = 0 := by
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem width_unique {k : Nat} {g : Group} {p : Nat}
    (positive : 0 < k) (normalized : 256 ^ (k - 1) ≤ p) (fits : p < 256 ^ k)
    (bounds : 0 < g.len ∧ 256 ^ (g.len - 1) ≤ g.prime ∧ g.prime < 256 ^ g.len)
    (equal : p = g.prime) : k = g.len := by
  subst p
  have lo : k - 1 < g.len :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 256)).mp (Nat.lt_of_le_of_lt normalized bounds.2.2)
  have hi : g.len - 1 < k :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 256)).mp (Nat.lt_of_le_of_lt bounds.2.1 fits)
  omega

theorem width_unique_word {k : Nat} {g : Group} {p : Nat}
    (positive : 0 < k) (normalized : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ p) (fits : p < 256 ^ k)
    (bounds : 0 < g.len ∧ 256 ^ (g.len - 1) ≤ g.prime ∧ g.prime < 256 ^ g.len)
    (aligned : g.len % 8 = 0) (equal : p = g.prime) : k = g.len := by
  subst p
  have lo : g.len - 1 < k :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 256)).mp (Nat.lt_of_le_of_lt bounds.2.1 fits)
  have primeFits := bounds.2.2
  rw [VG.Proof.Bignum.pow256_eq] at primeFits
  have hi : 64 * ((k + 7) / 8 - 1) < 8 * g.len :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt normalized primeFits)
  omega

theorem domain_parts {k : Nat} {dom : List Byte}
    (size : dom.length = 2 * k ∨ dom.length = 3 * k) :
    dom.take k ++ (dom.drop k).take k ++ (dom.drop (2 * k)).take k = dom := by
  rw [← List.take_add, show k + k = 2 * k by omega, ← List.take_add]
  exact List.take_of_length_le (by omega)

theorem domain_encoding {k : Nat} {dom : List Byte}
    (size : dom.length = 2 * k ∨ dom.length = 3 * k) :
    dom = i2osp (os2ip (dom.take k)) k ++ i2osp (os2ip ((dom.drop k).take k)) k ++
      if dom.length = 3 * k then i2osp (os2ip ((dom.drop (2 * k)).take k)) k else [] := by
  have lenP : (dom.take k).length = k := by simp only [List.length_take]; omega
  have lenG : ((dom.drop k).take k).length = k := by
    simp only [List.length_take, List.length_drop]; omega
  have invP : i2osp (os2ip (dom.take k)) k = dom.take k := by
    simpa only [lenP] using VG.Proof.Rsa.i2osp_os2ip (dom.take k)
  have invG : i2osp (os2ip ((dom.drop k).take k)) k = (dom.drop k).take k := by
    simpa only [lenG] using VG.Proof.Rsa.i2osp_os2ip ((dom.drop k).take k)
  rw [invP, invG]
  split
  · have lenQ : ((dom.drop (2 * k)).take k).length = k := by
      simp only [List.length_take, List.length_drop]; omega
    have invQ : i2osp (os2ip ((dom.drop (2 * k)).take k)) k = (dom.drop (2 * k)).take k := by
      simpa only [lenQ] using VG.Proof.Rsa.i2osp_os2ip ((dom.drop (2 * k)).take k)
    rw [invQ]
    exact (domain_parts size).symm
  · have empty : (dom.drop (2 * k)).take k = [] := by
      rw [List.drop_eq_nil_iff.mpr (by omega), List.take_nil]
    simpa only [empty, List.append_nil] using (domain_parts size).symm

theorem domainOf_injective {k : Nat} {left right : List Byte}
    (sizes : left.length = 2 * k ∨ left.length = 3 * k)
    (sameLength : left.length = right.length)
    (parameters : Spec.Ffdh.domainOf k left = Spec.Ffdh.domainOf k right) : left = right := by
  have rightSizes : right.length = 2 * k ∨ right.length = 3 * k := by omega
  have prime := congrArg Spec.Ffdh.Parameters.p parameters
  have generator := congrArg Spec.Ffdh.Parameters.g parameters
  have subgroup := congrArg Spec.Ffdh.Parameters.q parameters
  change os2ip (left.take k) = os2ip (right.take k) at prime
  change os2ip ((left.drop k).take k) = os2ip ((right.drop k).take k) at generator
  rw [domain_encoding sizes, domain_encoding rightSizes, prime, generator, sameLength]
  by_cases hasQ : right.length = 3 * k
  · have qvalue : os2ip ((left.drop (2 * k)).take k) = os2ip ((right.drop (2 * k)).take k) := by
      simpa only [Spec.Ffdh.domainOf, sameLength, hasQ, ite_true, Option.some.injEq] using subgroup
    rw [qvalue]
  · simp only [ite_eq_right hasQ]

theorem group_take_two (g : Group) :
    g.domain.take (2 * g.len) = i2osp g.prime g.len ++ i2osp 2 g.len := by
  unfold VG.Impl.Ffdh.VettedGroups.Group.domain
  rw [show 2 * g.len = (i2osp g.prime g.len ++ i2osp 2 g.len).length by
    simp only [List.length_append, VG.Proof.Rsa.i2osp_length]; omega]
  exact List.take_left

theorem group_take_three (g : Group) : g.domain.take (3 * g.len) = g.domain := by
  apply List.take_of_length_le
  simp only [VG.Impl.Ffdh.VettedGroups.Group.domain, List.length_append, VG.Proof.Rsa.i2osp_length]
  omega

theorem domainOf_two {k p g : Nat} (positive : 0 < k)
    (pfits : p < 256 ^ k) (gfits : g < 256 ^ k) :
    Spec.Ffdh.domainOf k (i2osp p k ++ i2osp g k) = ⟨p, g, none⟩ := by
  have different : k + k ≠ 3 * k := by omega
  have takeAll (x : Nat) : (i2osp x k).take k = i2osp x k :=
    List.take_of_length_le (by rw [VG.Proof.Rsa.i2osp_length];exact Nat.le_refl _)
  simp [Spec.Ffdh.domainOf, VG.Proof.Rsa.i2osp_length, takeAll,
    VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt pfits, Nat.mod_eq_of_lt gfits, different]

theorem domainOf_three {k p g q : Nat}
    (pfits : p < 256 ^ k) (gfits : g < 256 ^ k) (qfits : q < 256 ^ k) :
    Spec.Ffdh.domainOf k (i2osp p k ++ i2osp g k ++ i2osp q k) = ⟨p, g, some q⟩ := by
  have takeAll (x : Nat) : (i2osp x k).take k = i2osp x k :=
    List.take_of_length_le (by rw [VG.Proof.Rsa.i2osp_length];exact Nat.le_refl _)
  have dropAll : (i2osp p k).drop (k + k) = [] :=
    List.drop_eq_nil_iff.mpr (by rw [VG.Proof.Rsa.i2osp_length]; omega)
  simp [Spec.Ffdh.domainOf, List.drop_append, VG.Proof.Rsa.i2osp_length, takeAll, dropAll,
    VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt pfits, Nat.mod_eq_of_lt gfits,
    Nat.mod_eq_of_lt qfits, show k + (k + k) = 3 * k by omega, show 2 * k = k + k by omega]

def NumericMatch (g : Group) (a : Spec.Ffdh.Parameters) : Prop :=
  a.p = g.prime ∧ a.g = 2 ∧ (a.q = none ∨ a.q = some ((a.p - 1) / 2))

instance (g : Group) (a : Spec.Ffdh.Parameters) : Decidable (NumericMatch g a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def numericRecognize : List Group → Spec.Ffdh.Parameters → Nat
  | [], _ => 0
  | g :: gs, a => if NumericMatch g a then g.bits else numericRecognize gs a

theorem group_parameters (g : Group) (member : g ∈ groups) {n : Nat}
    (size : n = 2 * g.len ∨ n = 3 * g.len) :
    Spec.Ffdh.domainOf g.len (g.domain.take n) =
      ⟨g.prime, 2, if n = 3 * g.len then some ((g.prime - 1) / 2) else none⟩ := by
  have bounds := group_bounds g member
  have twoFits : 2 < 256 ^ g.len := by
    have : 256 ^ 1 ≤ 256 ^ g.len := Nat.pow_le_pow_right (by decide) bounds.1
    simp only [Nat.pow_one] at this
    omega
  rcases size with rfl | rfl
  · rw [group_take_two, domainOf_two bounds.1 bounds.2.2 twoFits,
      ite_eq_right (by have := bounds.1; omega : 2 * g.len ≠ 3 * g.len)]
  · rw [group_take_three]
    rw [ite_eq_left rfl]
    exact domainOf_three bounds.2.2 twoFits
      (show (g.prime - 1) / 2 < 256 ^ g.len by omega)

theorem group_match_iff {k : Nat} {dom : List Byte} (positive : 0 < k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k)
    (normalized : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ os2ip (dom.take k))
    (g : Group) (member : g ∈ groups) :
    (g.len = k ∧ dom = g.domain.take dom.length) ↔ NumericMatch g (Spec.Ffdh.domainOf k dom) := by
  have lenP : (dom.take k).length = k := by simp only [List.length_take]; omega
  constructor
  · rintro ⟨rfl, same⟩
    have parameters := congrArg (Spec.Ffdh.domainOf g.len) same
    rw [group_parameters g member size] at parameters
    unfold NumericMatch
    rw [parameters]
    refine ⟨rfl, rfl, ?_⟩
    split <;> simp
  · rintro ⟨prime, generator, subgroup⟩
    have bounds := group_bounds g member
    have fits := VG.Proof.Bignum.os2ip_lt (dom.take k)
    rw [lenP] at fits
    have sameWidth : k = g.len := width_unique_word positive normalized fits bounds (group_aligned g member) prime
    subst k
    refine ⟨rfl, ?_⟩
    apply domainOf_injective size
    · have domainLength : g.domain.length = 3 * g.len := by
        simp only [VG.Impl.Ffdh.VettedGroups.Group.domain, List.length_append,
          VG.Proof.Rsa.i2osp_length]
        omega
      simp only [List.length_take, domainLength]
      omega
    · rw [group_parameters g member size]
      change os2ip (dom.take g.len) = g.prime at prime
      change os2ip ((dom.drop g.len).take g.len) = 2 at generator
      unfold Spec.Ffdh.domainOf
      rw [prime, generator]
      by_cases hasQ : dom.length = 3 * g.len
      · simp only [Spec.Ffdh.domainOf, hasQ, ite_true, prime, Option.some.injEq,
          reduceCtorEq, false_or] at subgroup
        simp only [hasQ, ite_true, subgroup]
      · simp only [hasQ, ite_false]

theorem numericRecognize_spec (a : Spec.Ffdh.Parameters) :
    numericRecognize groups a = (Spec.Ffdh.vettedExponentBits a).getD 0 := by
  have guard : (a.g != 2 || (a.q.isSome && a.q != some ((a.p - 1) / 2))) = false ↔
      a.g = 2 ∧ (a.q = none ∨ a.q = some ((a.p - 1) / 2)) := by
    cases hq : a.q <;> simp [Bool.or_eq_false_iff]
  by_cases good : a.g = 2 ∧ (a.q = none ∨ a.q = some ((a.p - 1) / 2))
  · have flag := guard.mpr good
    rw [Spec.Ffdh.vettedExponentBits, flag]
    simp only [Bool.false_eq_true, ite_false]
    simp only [numericRecognize, VG.Impl.Ffdh.VettedGroups.groups, NumericMatch,
      good.1, good.2, and_self, and_true, Bool.or_eq_true, beq_iff_eq]
    have splitOr (p q : Prop) [Decidable p] [Decidable q] {α : Type} (x y : α) :
      (if p∨q then x else y)=(if p then x else if q then x else y) :=by
      by_cases hp:p <;>by_cases hq:q <;>simp only [hp,hq,true_or,or_true,false_or,ite_true,ite_false]
    simp only [splitOr]
    have getD_ite (p : Prop) [Decidable p] (x y : Option Nat) :
        (if p then x else y).getD 0 = if p then x.getD 0 else y.getD 0 := by
      by_cases hp : p <;> simp only [hp, ite_true, ite_false]
    simp only [getD_ite, Option.getD_some, Option.getD_none]
  · have flag : (a.g != 2 || (a.q.isSome && a.q != some ((a.p - 1) / 2))) = true := by
      cases h : (a.g != 2 || (a.q.isSome && a.q != some ((a.p - 1) / 2)))
      · exact False.elim (good (guard.mp h))
      · rfl
    have unmatched (g : Group) : ¬ NumericMatch g a := fun h => good h.2
    simp [numericRecognize, VG.Impl.Ffdh.VettedGroups.groups, unmatched,
      Spec.Ffdh.vettedExponentBits, flag]

theorem recognize_spec {k : Nat} {dom : List Byte} (positive : 0 < k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k)
    (normalized : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ os2ip (dom.take k)) :
    recognizeList groups k dom = (Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom)).getD 0 := by
  have aux : ∀ gs, (∀ g ∈ gs, g ∈ groups) →
      recognizeList gs k dom = numericRecognize gs (Spec.Ffdh.domainOf k dom) := by
    intro gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro members
      have equivalence := group_match_iff positive size normalized g (members g (by simp))
      rw [recognizeList, numericRecognize]
      by_cases matched : NumericMatch g (Spec.Ffdh.domainOf k dom)
      · rw [ite_eq_left (equivalence.mpr matched), ite_eq_left matched]
      · rw [ite_eq_right (fun h => matched (equivalence.mp h)), ite_eq_right matched]
        exact ih (fun x hx => members x (by simp [hx]))
  rw [aux groups (fun _ h => h)]
  exact numericRecognize_spec _

end VG.Proof.Ffdh.VettedGroupFacts
