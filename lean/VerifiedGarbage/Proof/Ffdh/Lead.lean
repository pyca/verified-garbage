module
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# FFDH: the leading zero octets of a number

`lead bs`: the number of zero octets that a scan for the first nonzero
octet of `bs` skips, stopping at the last octet. The octets from there are
the number (`os2ip_drop_lead`); the first of them is not zero, unless it is
the last (`lead_nonzero`).
-/

@[expose] public section

namespace VG.Proof.Ffdh

open VG

/-- The zero octets before the first nonzero one, or before the last octet. -/
def lead : List Byte → Nat
  | [] => 0
  | [_] => 0
  | b :: c :: bs => if b = 0 then lead (c :: bs) + 1 else 0

theorem lead_lt {bs : List Byte} (h : bs ≠ []) : lead bs < bs.length := by
  match bs, h with
  | [_], _ => simp [lead]
  | b :: c :: bs, _ =>
    have := lead_lt (bs := c :: bs) (by simp)
    simp only [lead, List.length_cons] at this ⊢
    split <;> omega

theorem lead_zero {bs : List Byte} : ∀ j < lead bs, ∃ h : j < bs.length, bs[j] = 0 := by
  match bs with
  | [] => simp [lead]
  | [_] => simp [lead]
  | b :: c :: bs =>
    intro j hj
    simp only [lead] at hj
    by_cases hb : b = 0
    · rw [ite_eq_left_iff.mpr (fun h => absurd hb h)] at hj
      cases j with
      | zero => exact ⟨by simp, hb⟩
      | succ j =>
        obtain ⟨h, h'⟩ := lead_zero (bs := c :: bs) j (by omega)
        exact ⟨by simp at h ⊢; omega, h'⟩
    · have e : lead (b :: c :: bs) = 0 := by simp only [lead]; exact ite_eq_right hb
      simp only [lead] at e; omega

/-- The octet the scan stops at is not zero, unless it is the last. -/
theorem lead_nonzero {bs : List Byte} (h : bs ≠ []) (hl : lead bs + 1 < bs.length) :
    bs[lead bs]'(lead_lt h) ≠ 0 := by
  match bs, h with
  | [_], _ => simp at hl
  | b :: c :: bs, _ =>
    by_cases hb : b = 0
    · have e : lead (b :: c :: bs) = lead (c :: bs) + 1 := by simp [lead, hb]
      have hl' : lead (c :: bs) + 1 < (c :: bs).length := by rw [e] at hl; simpa using hl
      simp only [e, List.getElem_cons_succ]
      exact lead_nonzero (bs := c :: bs) (by simp) hl'
    · have e : lead (b :: c :: bs) = 0 := by simp only [lead]; exact ite_eq_right hb
      simp only [e, List.getElem_cons_zero]
      exact hb

theorem os2ip_drop_lead (bs : List Byte) : Spec.Rsa.os2ip (bs.drop (lead bs)) = Spec.Rsa.os2ip bs := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | b :: c :: bs =>
    by_cases hb : b = 0
    · subst hb
      have e : lead ((0 : Byte) :: c :: bs) = lead (c :: bs) + 1 := by simp [lead]
      rw [e, List.drop_succ_cons, os2ip_drop_lead (c :: bs), VG.Proof.Bignum.os2ip_cons (0 : Byte)]
      simp
    · have e : lead (b :: c :: bs) = 0 := by simp only [lead]; exact ite_eq_right hb
      rw [e, List.drop_zero]

/-- The scan's result: the octets from `lead bs`. -/
theorem lead_drop_length (bs : List Byte) : (bs.drop (lead bs)).length = bs.length - lead bs := by
  simp

end VG.Proof.Ffdh
