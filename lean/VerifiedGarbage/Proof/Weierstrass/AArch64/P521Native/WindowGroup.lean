module

public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.RecodeMath
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Window5 Spec.Weierstrass

/-- All nonfinal signed additions are nonexceptional. The final digit is
handled separately by the measured implementation's complete addition path. -/
theorem window_noexc_nonfinal {C : Curve} (hC : Law C) (hO : PrimeOrder C) {P : Point C}
    (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn64 : 64≤C.n)
    {k J j : Nat} (hk : k<C.n) (hj : j<J) (h1 : 1≤j)
    (he : 1≤winE (k+16*Window5.geom J) J (j+1)) :
    mul (32*winE (k+16*Window5.geom J) J (j+1)) P≠winPt C P (k+16*Window5.geom J) j ∧
      Spec.Weierstrass.add (mul (32*winE (k+16*Window5.geom J) J (j+1)) P) (winPt C P (k+16*Window5.geom J) j)≠.infinity := by
  have hs := winE_step (k:=k+16*Window5.geom J) (J:=J) (j:=j) (Nat.le_add_left _ _) hj
  have hwl := winE_le k (J:=J) (j:=j) (by omega_arith)
  have hsub := winE_lt_sub hn64 hk (J:=J) (j:=j) (by omega_arith) h1
  have hv := Window5.nib_lt (k+16*Window5.geom J) j
  generalize hee : winE (k+16*Window5.geom J) J (j+1)=e at he hs ⊢
  generalize hw : winE (k+16*Window5.geom J) J j=w at hs hwl hsub
  generalize hvv : Window5.nib (k+16*Window5.geom J) j=v at hs hv
  refine ⟨fun eq => ?_,fun eq => ?_⟩
  · rw [winPt_zmul,hvv,←zmul_natCast] at eq
    have dvd := zmul_dvd hC hO hP hP0 eq
    exact not_dvd_of_pos_lt (n:=C.n) (x:=((32*e : Nat) : Int)-((v : Int)-16))
      (by omega_arith) (by omega_arith) dvd
  · rw [←hee,win_add hC hP (Nat.le_add_left _ _) hj,hw] at eq
    exact mul_ne_infinity hO hP hP0 (m:=w) (by omega_arith) (by omega_arith) eq

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

 def windowSelectF {F : Type _} [Lean.Grind.CommRing F] [DecidableEq F]
    (A E : F×F×F) : F×F×F :=
  if A.2.2=0 then E else if E.2.2=0 then A else maddJF A.1 A.2.1 A.2.2 E.1 E.2.1

 theorem window_select_group {C : Curve} (law : Law C) (ha : AM3 C)
    {A E : Fe C×Fe C×Fe C} {Q S : Point C}
    (hQ : onCurve C Q=true) (hS : onCurve C S=true)
    (ia : InvJ C A.1 A.2.1 A.2.2 Q) (ie : InvJ C E.1 E.2.1 E.2.2 S)
    (ez : E.2.2=0 ∨ E.2.2=1)
    (separate : Q≠.infinity → S≠.infinity → Q≠S) :
    InvJ C (windowSelectF A E).1 (windowSelectF A E).2.1 (windowSelectF A E).2.2
      (Spec.Weierstrass.add Q S) := by
  by_cases az : A.2.2=0
  · have q0 := (InvJ.z_zero_iff law ia).mp az
    rw [windowSelectF,ite_eq_left az,q0]
    exact ie
  · by_cases e0 : E.2.2=0
    · have s0 := (InvJ.z_zero_iff law ie).mp e0
      rw [windowSelectF,ite_eq_right az,ite_eq_left e0,s0]
      cases Q <;> exact ia
    · have e1 : E.2.2=1 := ez.resolve_left e0
      have rep := ie.rep_of_ne e0
      rw [e1,Lean.Grind.Semiring.mul_one,Lean.Grind.Semiring.mul_one,Lean.Grind.Semiring.mul_one] at rep
      have sa := rep.eq_affine law
      have qne : Q≠.infinity := fun h => az ((InvJ.z_zero_iff law ia).mpr h)
      have sne : S≠.infinity := fun h => e0 ((InvJ.z_zero_iff law ie).mpr h)
      have hs : onCurve C (.affine E.1 E.2.1)=true := by rw [←sa]; exact hS
      have hsep : Q≠.affine E.1 E.2.1 := by rw [←sa]; exact separate qne sne
      rw [windowSelectF,ite_eq_right az,ite_eq_right e0,sa]
      exact InvJ.madd law ha hQ hs ia az hsep

end VG.Proof.Weierstrass.AArch64.P521Native
