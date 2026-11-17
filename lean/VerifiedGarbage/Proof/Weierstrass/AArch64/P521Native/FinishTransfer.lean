module

-- separate module: generic modulus relabeling avoids unfolding nested point formulas and the concrete 521-bit prime in the API proof
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishGroup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjectiveState
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishFrontReady
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Weierstrass.AArch64.P521Native.FinishFront`, which this module and modules that import it used -/

section

/-! Adjacent stages of the final P-521 window, sharing their machine-state interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem finish_add_points_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (bp : canonicalPoint s.mem base 1072) (bq : canonicalPoint s.mem base 1504)
    (bb : wordsVal s.mem base 568 9<fieldPrime) :
    WP isa finishAddMachine s fun t =>
      canonicalPoint t.mem base 1288 ∧
      ordinaryPoint t.mem base 1288=rcbAdd3 (Fin.ofNat fieldPrime (wordsVal s.mem base 568 9))
        (ordinaryPoint s.mem base 1072).1 (ordinaryPoint s.mem base 1072).2.1 (ordinaryPoint s.mem base 1072).2.2
        (ordinaryPoint s.mem base 1504).1 (ordinaryPoint s.mem base 1504).2.1 (ordinaryPoint s.mem base 1504).2.2 ∧
      Scr t base 8192 ∧ FieldPublic s t ∧ Unch base (fieldProgramWrites id finishAddOps) s.mem t.mem := by
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal s.mem base d 9)
  have inv : OrdinaryInv base fieldPrime id [1072,1144,1216,1504,1576,1648,568] E (fun _ => 1) s := by
    constructor
    · intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · simpa only [id_eq,Nat.one_mul] using bp.1
      · simpa only [id_eq,Nat.one_mul] using bp.2.1
      · simpa only [id_eq,Nat.one_mul] using bp.2.2
      · simpa only [id_eq,Nat.one_mul] using bq.1
      · simpa only [id_eq,Nat.one_mul] using bq.2.1
      · simpa only [id_eq,Nat.one_mul] using bq.2.2
      · simpa only [id_eq,Nat.one_mul] using bb
    · intro d _; rfl
  refine WP.mono (finish_add_machine_ok hs inv) fun t ⟨it,ht,kt,ft⟩ => ?_
  have xb := it.bound 1288 (by decide)
  have yb := it.bound 1360 (by decide)
  have zb := it.bound 1432 (by decide)
  have xv := it.value 1288 (by decide)
  have yv := it.value 1360 (by decide)
  have zv := it.value 1432 (by decide)
  change Fin.ofNat fieldPrime (wordsVal t.mem base 1288 9)=pointRun finishAddOps E 1288 at xv
  change Fin.ofNat fieldPrime (wordsVal t.mem base 1360 9)=pointRun finishAddOps E 1360 at yv
  change Fin.ofNat fieldPrime (wordsVal t.mem base 1432 9)=pointRun finishAddOps E 1432 at zv
  refine ⟨⟨by simpa only [id_eq,Nat.one_mul] using xb,
    by simpa only [id_eq,Nat.one_mul] using yb,by simpa only [id_eq,Nat.one_mul] using zb⟩,?_,ht,kt,field_program_frame_unch ft⟩
  change (Fin.ofNat fieldPrime (wordsVal t.mem base 1288 9),Fin.ofNat fieldPrime (wordsVal t.mem base 1360 9),
    Fin.ofNat fieldPrime (wordsVal t.mem base 1432 9))=_
  rw [xv,yv,zv,finishAdd_value]
  rfl

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def finishSelectedSum : Prog isa := .seq (.block finishLookupCode) finishAddMachine
def finishSelectedWrites : List (Nat × Nat) :=
  [(1504,216),(2224,72)]++fieldProgramWrites id finishAddOps

theorem finish_selected_sum_ok {base table : Addr} {s : State} {k : Nat}
    (hs : Scr s base 8192) (bp : canonicalPoint s.mem base 1072)
    (bb : wordsVal s.mem base 568 9<fieldPrime)
    (ht : LookupTableReadable s table) (zero : wordsVal s.mem base 280 9=0)
    (canonical : WindowTableCanonical s.mem table) (counter : s.gpr .x19=0#64)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa finishSelectedSum s fun t =>
      canonicalPoint t.mem base 1288 ∧
      ordinaryPoint t.mem base 1288=rcbAdd3 (Fin.ofNat fieldPrime (wordsVal s.mem base 568 9))
        (ordinaryPoint s.mem base 1072).1 (ordinaryPoint s.mem base 1072).2.1 (ordinaryPoint s.mem base 1072).2.2
        (windowAffine s.mem table k 0).1 (windowAffine s.mem table k 0).2.1 (windowAffine s.mem table k 0).2.2 ∧
      Scr t base 8192 ∧ FieldPublic s t ∧ Unch base finishSelectedWrites s.mem t.mem := by
  rw [finishSelectedSum,WP.seq_iff,finish_lookup_source,window_lookup_source]
  refine WP.mono (window_lookup_point_ok hs (by decide) (by decide : 0<105) ht zero canonical counter bits)
    fun u ⟨bq,qv,hu,ku,_,fu,_⟩ => ?_
  have pSame : ordinaryPoint u.mem base 1072=ordinaryPoint s.mem base 1072 := by
    simp only [ordinaryPoint]
    rw [fu.wordsVal (by decide) (by decide) (by decide),fu.wordsVal (by decide) (by decide) (by decide),
      fu.wordsVal (by decide) (by decide) (by decide)]
  have bpu : canonicalPoint u.mem base 1072 := by
    change wordsVal u.mem base 1072 9<fieldPrime ∧ wordsVal u.mem base 1144 9<fieldPrime ∧ wordsVal u.mem base 1216 9<fieldPrime
    rw [fu.wordsVal (by decide) (by decide) (by decide),fu.wordsVal (by decide) (by decide) (by decide),
      fu.wordsVal (by decide) (by decide) (by decide)]
    exact bp
  have bSame : wordsVal u.mem base 568 9=wordsVal s.mem base 568 9 := fu.wordsVal (by decide) (by decide) (by decide)
  have bbu : wordsVal u.mem base 568 9<fieldPrime := by rw [bSame]; exact bb
  have uf : Unch base [(1504,216),(2224,72)] s.mem u.mem := by
    intro x hx
    exact fu x (hx (1504,216) (by simp)) (hx (2224,72) (by simp))
  refine WP.mono (finish_add_points_ok hu bpu bq bbu) fun t ⟨bt,pt,ht,kt,ut⟩ => ?_
  rw [pSame,qv,bSame] at pt
  exact ⟨bt,pt,ht,ku.trans kt,uf.trans ut⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def finishFront : Prog isa := .seq finishFrontReady finishSelectedSum
def finishAllFrontWrites := finishFrontWrites++finishSelectedWrites

def finishSum (m : Mem) (base table : Addr) (k : Nat) :=
  let P := finishHomogeneous (finishDbl5 (ordinaryPoint m base 1072))
  let Q := windowAffine m table k 0
  rcbAdd3 (Fin.ofNat fieldPrime (wordsVal m base 568 9)) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

theorem finish_front_ok {s : State} {table : Addr} {k : Nat}
    (hs : Scr s (s.gpr .x0) 8192) (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) (zero : wordsVal s.mem (s.gpr .x0) 280 9=0)
    (bb : wordsVal s.mem (s.gpr .x0) 568 9<fieldPrime) (oneBound : 1<fieldPrime)
    (apart : TableWorkspaceApart (s.gpr .x0) table 8192) (tableRead : LookupTableReadable s table)
    (canonical : WindowTableCanonical s.mem table)
    (bits : ∀i<525,s.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) :
    WP isa finishFront s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=finishSum s.mem (s.gpr .x0) table k ∧
      Scr t (s.gpr .x0) 8192 ∧ Unch (s.gpr .x0) finishAllFrontWrites s.mem t.mem ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFront,WP.seq_iff]
  refine WP.mono (finish_front_ready_ok hs bound counter zero bb oneBound apart tableRead canonical bits)
    fun u ⟨bp,pv,hu,rt,ct,bt,zu,bu,cu,g20,g26,uf,rd,wr,sp,g27,g28,v31⟩ => ?_
  have tableSame := finish_affine_keep apart uf (by decide) k 0
  have bSame : wordsVal u.mem (s.gpr .x0) 568 9=wordsVal s.mem (s.gpr .x0) 568 9 := uf.wordsVal (by decide) (by decide)
  refine WP.mono (finish_selected_sum_ok hu bp bu rt zu ct cu bt) fun t ⟨boundT,value,ht,kt,ut⟩ => ?_
  rw [pv,tableSame,bSame] at value
  refine ⟨boundT,value,ht,uf.trans ut,kt.rd.trans rd,kt.wr.trans wr,kt.sp.trans sp,?_,?_,?_,?_,kt.v31.trans v31⟩
  · exact (kt.gpr .x20 (by decide)).trans g20
  · exact (kt.gpr .x26 (by decide)).trans g26
  · exact (kt.gpr .x27 (by decide)).trans g27
  · exact (kt.gpr .x28 (by decide)).trans g28

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

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
