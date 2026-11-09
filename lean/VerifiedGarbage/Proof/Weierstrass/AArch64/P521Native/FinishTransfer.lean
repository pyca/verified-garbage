module

-- separate module: generic modulus relabeling avoids unfolding nested point formulas and the concrete 521-bit prime in the API proof

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishGroup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup

/-! Relabel the ordinary machine field as the curve field without evaluating
its 521-bit prime in the elaborator. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field (ordinaryPoint)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

private theorem finish_finite_one {p : Nat} [NeZero p] : Fin.ofNat p 1=(1 : Fin p) := rfl

theorem final_five_machine (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) : finalFive A=finishDbl5 A := rfl

theorem final_homogeneous_machine (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    finalHomogeneous A=finishHomogeneous A := by
  simp only [finalHomogeneous,finishHomogeneous,finish_finite_one]

def windowAffineAt (C : Curve) (m : Mem) (table : Addr) (k j : Nat) : Fe C×Fe C×Fe C :=
  let d := magH 16 (combWin 5 k j)
  (Fin.ofNat C.p (windowX m table d),
   Fin.ofNat C.p (if combWin 5 k j<16 then (C.p-windowY m table d)%C.p else windowY m table d),
   Fin.ofNat C.p (if d=0 then 0 else 1))

def finishSumAt (C : Curve) (m : Mem) (base table : Addr) (k : Nat) :=
  let A := finalHomogeneous (finalFive (pointAt C m base 1072))
  let D := windowAffineAt C m table k 0
  rcbAdd3 (Fin.ofNat C.p (wordsVal m base 568 9)) A.1 A.2.1 A.2.2 D.1 D.2.1 D.2.2

def finishSumN (p : Nat) [NeZero p] (m : Mem) (base table : Addr) (k : Nat) : Fin p×Fin p×Fin p :=
  let A : Fin p×Fin p×Fin p := (Fin.ofNat p (wordsVal m base 1072 9),
    Fin.ofNat p (wordsVal m base 1144 9),Fin.ofNat p (wordsVal m base 1216 9))
  let H := finalHomogeneous (finalFive A)
  let d := magH 16 (combWin 5 k 0)
  let D : Fin p×Fin p×Fin p := (Fin.ofNat p (windowX m table d),
    Fin.ofNat p (if combWin 5 k 0<16 then (p-windowY m table d)%p else windowY m table d),
    Fin.ofNat p (if d=0 then 0 else 1))
  rcbAdd3 (Fin.ofNat p (wordsVal m base 568 9)) H.1 H.2.1 H.2.2 D.1 D.2.1 D.2.2

theorem finish_sum_n_curve (C : Curve) (m : Mem) (base table : Addr) (k : Nat) :
    finishSumN C.p m base table k=finishSumAt C m base table k := by
  simp only [finishSumN,finishSumAt,pointAt,windowAffineAt]

theorem finish_sum_n_machine (m : Mem) (base table : Addr) (k : Nat) :
    finishSumN fieldPrime m base table k=finishSum m base table k := by
  simp only [finishSumN,finishSum,ordinaryPoint,final_five_machine,final_homogeneous_machine,windowAffine]

private theorem sum_coordinate_relabel {p q : Nat} [NeZero p] [NeZero q] (eq : p=q)
    {m : Mem} {base table : Addr} {k X Y Z : Nat}
    (value : (Fin.ofNat p X,Fin.ofNat p Y,Fin.ofNat p Z)=finishSumN p m base table k) :
    (Fin.ofNat q X,Fin.ofNat q Y,Fin.ofNat q Z)=finishSumN q m base table k := by
  cases eq
  exact value

private theorem sum_value_relabel {p q : Nat} [np : NeZero p] [nq : NeZero q] (eq : p=q)
    {m : Mem} {base table : Addr} {k xo : Nat}
    (value : Fin.ofNat p xo=(finishSumN p m base table k).1*(finishSumN p m base table k).2.2^(p-2)) :
    Fin.ofNat q xo=(finishSumN q m base table k).1*(finishSumN q m base table k).2.2^(q-2) := by
  cases eq
  have same : np=nq := Subsingleton.elim _ _
  cases same
  exact value

theorem finish_sum_coordinate_transfer {C : Curve} (hp : C.p=fieldPrime)
    {m m' : Mem} {base table : Addr} {k : Nat}
    (value : ordinaryPoint m' base 1288=finishSum m base table k) :
    pointAt C m' base 1288=finishSumAt C m base table k := by
  have native : (Fin.ofNat fieldPrime (wordsVal m' base 1288 9),
    Fin.ofNat fieldPrime (wordsVal m' base 1360 9),Fin.ofNat fieldPrime (wordsVal m' base 1432 9))=
      finishSumN fieldPrime m base table k := by
    simpa only [finish_sum_n_machine,ordinaryPoint] using value
  have transferred := sum_coordinate_relabel hp.symm native
  rw [finish_sum_n_curve] at transferred
  simpa only [pointAt] using transferred

theorem finish_value_transfer {C : Curve} (hp : C.p=fieldPrime)
    {m : Mem} {base table : Addr} {k xo : Nat}
    (value : Fin.ofNat fieldPrime xo=(finishSum m base table k).1*(finishSum m base table k).2.2^(fieldPrime-2)) :
    Fin.ofNat C.p xo=(finishSumAt C m base table k).1*(finishSumAt C m base table k).2.2^(C.p-2) := by
  have native : Fin.ofNat fieldPrime xo=(finishSumN fieldPrime m base table k).1*
      (finishSumN fieldPrime m base table k).2.2^(fieldPrime-2) := by
    simpa only [finish_sum_n_machine,ordinaryPoint] using value
  have transferred := sum_value_relabel hp.symm native
  rw [finish_sum_n_curve] at transferred
  exact transferred

private theorem sum_zero_relabel {p q : Nat} [np : NeZero p] [nq : NeZero q] (eq : p=q)
    (m : Mem) (base table : Addr) (k : Nat) :
    (finishSumN p m base table k).2.2=0 ↔ (finishSumN q m base table k).2.2=0 := by
  cases eq
  have same : np=nq := Subsingleton.elim _ _
  cases same
  rfl

theorem finish_zero_transfer {C : Curve} (hp : C.p=fieldPrime)
    (m : Mem) (base table : Addr) (k : Nat) :
    (finishSum m base table k).2.2=0 ↔ (finishSumAt C m base table k).2.2=0 := by
  have result := sum_zero_relabel hp.symm m base table k
  simpa only [finish_sum_n_machine,finish_sum_n_curve] using result

theorem finish_sum_rep {C : Curve} (law : Law C) (ha : AM3 C) {m : Mem} {base table : Addr}
    {d k : Nat} (offset : k=d+16*Window5.geom 105) {P : Point C} (hP : onCurve C P=true)
    (b : Fin.ofNat C.p (wordsVal m base 568 9)=Fin.ofNat C.p C.b)
    (current : InvJ C (pointAt C m base 1072).1 (pointAt C m base 1072).2.1 (pointAt C m base 1072).2.2
      (mul (Window5.winE k 105 1) P))
    (digit : RepA C (windowAffineAt C m table k 0).1 (windowAffineAt C m table k 0).2.1
      (windowAffineAt C m table k 0).2.2 (Window5.winPt C P k 0)) :
    Rep C (finishSumAt C m base table k).1 (finishSumAt C m base table k).2.1
      (finishSumAt C m base table k).2.2 (mul d P) := by
  subst k
  have result := final_digit_group law ha hP current digit
  simpa only [finishSumAt,finalSum,b] using result

end VG.Proof.Weierstrass.AArch64.P521Native
