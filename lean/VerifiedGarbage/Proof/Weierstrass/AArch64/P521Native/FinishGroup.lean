module

public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrontReady
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete final-digit group law and the existing ECDH API specification. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

def finalDouble {F : Type _} [Lean.Grind.CommRing F] (A : F×F×F) := dblJF A.1 A.2.1 A.2.2
def finalFive {F : Type _} [Lean.Grind.CommRing F] (A : F×F×F) :=
  finalDouble (finalDouble (finalDouble (finalDouble (finalDouble A))))
def finalHomogeneous {F : Type _} [Lean.Grind.CommRing F] [DecidableEq F] (A : F×F×F) :=
  (A.1*A.2.2,(if A.2.2*A.2.2*A.2.2=0 then 1 else A.2.1),A.2.2*A.2.2*A.2.2)

theorem final_five_inv {C : Curve} (law : Law C) (ha : AM3 C) {P : Point C}
    (hP : onCurve C P=true) {A : Fe C×Fe C×Fe C} {m : Nat}
    (ia : InvJ C A.1 A.2.1 A.2.2 (mul m P)) :
    InvJ C (finalFive A).1 (finalFive A).2.1 (finalFive A).2.2 (mul (32*m) P) := by
  have step {B : Fe C×Fe C×Fe C} {n : Nat} (ib : InvJ C B.1 B.2.1 B.2.2 (mul n P)) :
      InvJ C (finalDouble B).1 (finalDouble B).2.1 (finalDouble B).2.2 (mul (2*n) P) := by
    have doubled := InvJ.dbl law ha (law.onCurve_mul hP n) ib
    rw [law.add_mul_mul hP] at doubled
    have ar : n+n=2*n := by omega_arith
    rw [ar] at doubled
    exact doubled
  have i1 := step ia
  have i2 := step i1
  have i3 := step i2
  have i4 := step i3
  have i5 := step i4
  have ar : 2*(2*(2*(2*(2*m))))=32*m := by omega_arith
  rw [ar] at i5
  exact i5

theorem final_homogeneous_rep {C : Curve} (law : Law C) {A : Fe C×Fe C×Fe C} {Q : Point C}
    (ia : InvJ C A.1 A.2.1 A.2.2 Q) :
    Rep C (finalHomogeneous A).1 (finalHomogeneous A).2.1 (finalHomogeneous A).2.2 Q := by
  by_cases hz : A.2.2=0
  · have q0 := (InvJ.z_zero_iff law ia).mp hz
    rw [finalHomogeneous,hz,q0]
    simpa only [Lean.Grind.Semiring.mul_zero,ite_true] using rep_infinity' law
  · have cube := cube_ne_zero law hz
    simpa only [finalHomogeneous,cube,ite_false] using ia.rep_of_ne hz

def finalSum {C : Curve} (A D : Fe C×Fe C×Fe C) :=
  let H := finalHomogeneous (finalFive A)
  rcbAdd3 (Fin.ofNat C.p C.b) H.1 H.2.1 H.2.2 D.1 D.2.1 D.2.2

/-- The last complete addition needs no nonexceptional-point hypothesis. -/
theorem final_digit_group {C : Curve} (law : Law C) (ha : AM3 C) {P : Point C}
    (hP : onCurve C P=true) {A D : Fe C×Fe C×Fe C} {d : Nat}
    (ia : InvJ C A.1 A.2.1 A.2.2 (mul (Window5.winE (d+16*Window5.geom 105) 105 1) P))
    (id : RepA C D.1 D.2.1 D.2.2 (Window5.winPt C P (d+16*Window5.geom 105) 0)) :
    Rep C (finalSum A D).1 (finalSum A D).2.1 (finalSum A D).2.2 (mul d P) := by
  have five := final_five_inv law ha hP ia
  have homogeneous := final_homogeneous_rep law five
  have sum := law.add3 ha (law.onCurve_mul hP _) (Window5.onCurve_winPt law hP _ _) homogeneous id.1
    (show rcbAdd3 (Fin.ofNat C.p C.b) (finalHomogeneous (finalFive A)).1
      (finalHomogeneous (finalFive A)).2.1 (finalHomogeneous (finalFive A)).2.2 D.1 D.2.1 D.2.2=
      ((finalSum A D).1,(finalSum A D).2.1,(finalSum A D).2.2) from rfl)
  rw [Window5.win_add law hP (Nat.le_add_left _ _) (by decide : 0<105),Window5.winE_zero'] at sum
  exact sum

end VG.Proof.Weierstrass.AArch64.P521Native
