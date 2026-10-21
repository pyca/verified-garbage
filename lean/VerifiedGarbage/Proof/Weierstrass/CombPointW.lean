module

public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW

/-! Convert a selected Montgomery comb entry into the shared group-law invariant. -/

@[expose] public section
namespace VG.Proof.Weierstrass
open Spec.Weierstrass

theorem combEntry_rep {C : Curve} (hC : Law C) {w J j a R one : Nat}
    {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : CombOkW C w J tbl start) (unit : UnitMod C.p R)
    (hone : toM C.p R one=1) (hj : j<J) (ha : a≤2^(w-1)) :
    Rep C (toM C.p R (if a=0 then 0 else (combAt tbl j (a-1)).1*R%C.p))
      (toM C.p R (if a=0 then one else (combAt tbl j (a-1)).2*R%C.p))
      (toM C.p R (if a=0 then 0 else one)) (combPtW C w j a) := by
  by_cases zero : a=0
  · subst a
    simp only [↓reduceIte,toM_zero,hone,combPtW,Nat.zero_mul,Spec.Weierstrass.mul]
    exact rep_infinity' hC
  · simp only [zero,↓reduceIte,toM_mont unit,hone]
    have entry := h.entry j hj (a-1) (by omega)
    rw [Nat.sub_add_cancel (show 1≤a by omega)] at entry
    unfold combPtW
    rw [entry]
    exact rep_affine' hC _ _

theorem combSigned_rep {C : Curve} (hC : Law C) {w J j k R one : Nat}
    {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : CombOkW C w J tbl start) (unit : UnitMod C.p R)
    (hone : toM C.p R one=1) (hj : j<J) (hw : 1≤w)
    {x y z : Nat}
    (hx : x=(if magH (2^(w-1)) (combWin w k j)=0 then 0 else
      (combAt tbl j (magH (2^(w-1)) (combWin w k j)-1)).1*R%C.p))
    (hy : y=(if magH (2^(w-1)) (combWin w k j)=0 then one else
      (combAt tbl j (magH (2^(w-1)) (combWin w k j)-1)).2*R%C.p))
    (hz : z=(if magH (2^(w-1)) (combWin w k j)=0 then 0 else one))
    (hlt : y<C.p) :
    Rep C (toM C.p R x)
      (toM C.p R (if 2^(w-1)≤combWin w k j then y else (C.p-y)%C.p))
      (toM C.p R z) (signedPtW C w k j) := by
  have bound : magH (2^(w-1)) (combWin w k j)≤2^(w-1) := by
    apply magH_le
    have pow : 2^w=2*2^(w-1) := by
      calc
        2^w=2^((w-1)+1) := congrArg (fun n => 2^n) (by omega)
        _ = 2*2^(w-1) := by rw [Nat.pow_succ,Nat.mul_comm]
    rw [← pow]
    exact combWin_lt w k j
  have rep := combEntry_rep hC h unit hone hj bound
  rw [← hx,← hy,← hz] at rep
  unfold signedPtW
  by_cases pos : 2^(w-1)≤combWin w k j
  · simp only [pos,↓reduceIte]
    simpa only [magH,pos,↓reduceIte] using rep
  · simp only [pos,↓reduceIte]
    have neg : toM C.p R ((C.p-y)%C.p) = -toM C.p R y := by
      have sub := toM_sub (m := C.p) (R := R) (A := 0) (B := y) (by omega)
      simp only [Nat.zero_add,toM_zero] at sub
      grind
    rw [neg]
    exact Rep.negY (by simpa only [magH,pos,↓reduceIte] using rep)

end VG.Proof.Weierstrass
