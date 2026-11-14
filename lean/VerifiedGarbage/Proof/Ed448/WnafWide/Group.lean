module

public import VerifiedGarbage.Impl.Ed448.PublicTable
public import VerifiedGarbage.Proof.X448.BaseTable
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X448.BaseAdd
public import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding
import Mathlib.Tactic.Abel

/-! ### `Ed448.WnafWide.Table`, which only this module used -/

section

/-! Every public verification entry is the stated odd multiple of B. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open VG.Spec.X448 (Fe)
open VG.Proof.X448 (basePt basePt_rep)

private def checkRow (step p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y) &&
      checkRow step (pointAdd (basePt q) step) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (basePt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq] at hc
    have hq : Rep (basePt q) a := basePt_rep h hc.1.1 hc.1.2
    cases i with
    | zero => rw [List.getD_cons_zero, zero_nsmul, zero_add]; exact hq
    | succ i =>
      have hh := ih _ _ (pointAdd_rep hq hb) hc.2 i (by simp only [List.length_cons] at hi; omega_using [hi])
      rw [List.getD_cons_succ, succ_nsmul, add_assoc, add_comm c a]
      exact hh

private theorem table_check :
    checkRow (pointAdd basePoint basePoint) basePoint Impl.Ed448.PublicTable.rows = true := by
  decide +kernel

theorem publicTable_length : Impl.Ed448.PublicTable.rows.length = 64 := by decide +kernel

theorem publicTable_rep (i : Nat) (hi : i < 64) :
    Rep (basePt (Impl.Ed448.PublicTable.entry i)) ((2 * i + 1) • baseAff) := by
  have h2 : Rep (pointAdd basePoint basePoint) ((2 : Nat) • baseAff) := by
    rw [two_nsmul]
    exact pointAdd_rep basePoint_rep basePoint_rep
  have h := checkRow_ok _ _ _ _ h2 basePoint_rep _ table_check i (by rw [publicTable_length]; exact hi)
  simpa only [smul_smul, add_nsmul, one_nsmul, Nat.mul_comm, Impl.Ed448.PublicTable.entry] using h

end VG.Proof.Ed448.WnafWide

end

end


/-! The joint signed loop represents both complete unreduced scalars. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open VG.Proof.X448 (basePt addPt addPt_rep)
open VG.Impl.Ed448.WnafWide (residual digitAt)

def signedPoint (negative : Bool) (p : Point) : Point := if negative then negPoint p else p

theorem signed_abs (d : Int) :
    (if decide (d<0) then -(d.natAbs : Int) else d.natAbs)=d := by
  by_cases hd:d<0 <;> simp only [hd,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false] <;> omega_using [hd]

theorem signedPoint_rep {p : Point} {a : EPoint dZ} {n : Nat} (h:Rep p (n • a)) (b:Bool) :
    Rep (signedPoint b p) ((if b then -(n : Int) else n) • a) := by
  cases b
  · simpa only [signedPoint,Bool.false_eq_true,ite_false,natCast_zsmul] using h
  · simpa only [signedPoint,ite_true,neg_zsmul,natCast_zsmul] using h.neg

def baseEntry (d : Int) : Point :=
  if d=0 then identity else
    signedPoint (decide (d<0)) (basePt (Impl.Ed448.PublicTable.entry (d.natAbs/2)))

theorem baseEntry_rep {d : Int} (hd:-127≤d ∧ d≤127) (ho:d=0 ∨ d.natAbs%2=1) :
    Rep (baseEntry d) (d • baseAff) := by
  by_cases h0:d=0
  · subst d
    simpa only [baseEntry,ite_true,zero_smul] using identity_rep
  · have ha:d.natAbs<128 := by omega_using [hd]
    have he:2*(d.natAbs/2)+1=d.natAbs := by omega_using [ho, h0]
    have h:=publicTable_rep (d.natAbs/2) (by omega_using [hd])
    rw [he] at h
    have hsign:=signedPoint_rep h (decide (d<0))
    rw [signed_abs] at hsign
    simpa only [baseEntry,h0,ite_false] using hsign

def oddPoint (p : Point) : Nat → Point
  | 0 => p
  | n+1 => addPt (oddPoint p n) (double p)

theorem oddPoint_rep {p : Point} {a : EPoint dZ} (h:Rep p a) (n:Nat) :
    Rep (oddPoint p n) ((2*n+1) • a) := by
  induction n with
  | zero => simpa only [oddPoint,Nat.mul_zero,Nat.zero_add,one_nsmul] using h
  | succ n ih =>
    have hh:=addPt_rep ih (double_rep h)
    rw [←two_nsmul,←add_nsmul] at hh
    have he:2*n+1+2=2*(n+1)+1 := by omega_using []
    simpa only [oddPoint,he] using hh

def keyEntry (p : Point) (d : Int) : Point :=
  if d=0 then identity else signedPoint (decide (d<0)) (oddPoint p (d.natAbs/2))

theorem keyEntry_rep {p : Point} {a : EPoint dZ} (h:Rep p a) {d : Int}
    (ho:d=0 ∨ d.natAbs%2=1) : Rep (keyEntry p d) (d • a) := by
  by_cases h0:d=0
  · subst d
    simpa only [keyEntry,ite_true,zero_smul] using identity_rep
  · have he:2*(d.natAbs/2)+1=d.natAbs := by omega_using [ho, h0]
    have hh:=oddPoint_rep h (d.natAbs/2)
    rw [he] at hh
    have hh':=signedPoint_rep hh (decide (d<0))
    rw [signed_abs] at hh'
    simpa only [keyEntry,h0,ite_false] using hh'

def maybeAdd (d : Int) (p q : Point) : Point := if d=0 then p else addPt p q

theorem maybeAdd_rep {p q : Point} {a b : EPoint dZ} {d : Int}
    (hp:Rep p a) (hq:Rep q (d • b)) : Rep (maybeAdd d p q) (a+d • b) := by
  by_cases h0:d=0
  · simpa only [maybeAdd,h0,ite_true,zero_smul,add_zero] using hp
  · rw [maybeAdd,ite_eq_right h0]
    exact addPt_rep hp hq

theorem round_rep {p q : Point} {a : EPoint dZ} {S K n : Nat}
    (hp:Rep p ((residual true S (n+1) : Int) • baseAff+(residual false K (n+1) : Int) • a))
    (hq:Rep q ((digitAt false K n) • a)) :
    Rep (maybeAdd (digitAt false K n)
      (maybeAdd (digitAt true S n) (double p) (baseEntry (digitAt true S n))) q)
      ((residual true S n : Int) • baseAff+(residual false K n : Int) • a) := by
  have hb:=digit_bounds true (residual true S n)
  have hb':-127≤digitAt true S n ∧ digitAt true S n≤127 := by
    change (-128 : Int)<Impl.Ed448.WnafWide.digit true (residual true S n) ∧
      Impl.Ed448.WnafWide.digit true (residual true S n)<128 at hb
    change -127≤Impl.Ed448.WnafWide.digit true (residual true S n) ∧
      Impl.Ed448.WnafWide.digit true (residual true S n)≤127
    omega_using [hb]
  have he:=maybeAdd_rep (maybeAdd_rep (double_rep hp)
    (baseEntry_rep hb' (digit_zero_or_odd true _))) hq
  convert he using 1
  rw [residual_step true S n,residual_step false K n,add_zsmul,add_zsmul,
    mul_smul,mul_smul,two_zsmul,two_zsmul]
  simp only [digitAt]
  abel

end VG.Proof.Ed448.WnafWide
