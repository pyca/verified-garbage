module

public import VerifiedGarbage.Proof.P256.VerifyTable.Build
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import all Init.Data.Nat.Bitwise.Basic

/-! The co-Z table's values: entry `a` of the build's environment is
`(2a-1)Q` in Jacobian coordinates, with its `Z²` and `Z³`. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.Window5
open Spec.Weierstrass
open VG.Proof.P256.EcdhJac (tblW tblσ dbluN zadduN)

theorem ops_eq (d : Bool) : ops d=(if d then dbluN else zadduN).map (FOp.rename tblσ) := by
  cases d <;> rfl

theorem ops_out (d : Bool) : ∀ op∈(if d then dbluN else zadduN),op.out<13 := by
  cases d <;> decide

theorem ops_at (d : Bool) (e : Nat → Fe C) (i : Nat) :
    runOps (ops d) e (tblσ i)=runOps (if d then dbluN else zadduN) (fun j => e (tblσ j)) i := by
  have nd : tblW.Nodup := by decide
  have hp : ∀ x∈[1280,1440,224],x∉tblW := by decide
  rw [ops_eq]
  refine congrFun (runOps_rename tblσ _ e fun op hop y => ?_) i
  exact getD_append_inj nd hp (hp _ (by decide)) (by simpa [tblW] using ops_out d op hop) y

theorem ops_keep (d : Bool) (e : Nat → Fe C) {x : Nat} (hx : x∉tblW) : runOps (ops d) e x=e x := by
  apply runOps_of_not_out
  intro op hop he
  apply hx
  rw [← he]
  have : ∀ op∈ops d,op.out∈tblW := by cases d <;> decide
  exact this op hop

theorem copiesEnv_keep {F : Type _} : ∀ (l : List (Nat × Nat)) (E : Nat → F) {x : Nat},
    x∉l.map Prod.fst → copiesEnv l E x=E x
  | [], _, _, _ => rfl
  | p :: l, E, x, hx => by
    simp only [List.map_cons,List.mem_cons,not_or] at hx
    rw [copiesEnv,copiesEnv_keep l _ hx.2,Function.update_of_ne hx.1]

/-- The co-Z state after `k` steps: `D = 2Q` and `E = (2k+1)Q` at one `Z`,
its powers, and the first `k+1` entries. -/
structure CoZ (Q : Point C) (k : Nat) (F : Nat → Fe C) : Prop where
  d : InvJ C (F 608) (F 640) (F 768) (mul 2 Q)
  e : InvJ C (F 704) (F 736) (F 768) (mul (2*k+1) Q)
  z : F 768≠0
  z2 : F 5400=F 768*F 768
  z3 : F 5432=F 5400*F 768
  tbl : ∀ a,1≤a → a≤k+1 → InvJ C (F (dst a 0)) (F (dst a 1)) (F (dst a 2)) (mul (2*a-1) Q)
  c2 : ∀ a,1≤a → a≤k+1 → F (dst a 3)=F (dst a 2)*F (dst a 2)
  c3 : ∀ a,1≤a → a≤k+1 → F (dst a 4)=F (dst a 3)*F (dst a 2)

theorem dst_tblW {a j : Nat} (ha : 1≤a) (ha9 : a≤9) (hj : j<5) : dst a j∉tblW := by
  have h : ∀ a<9,∀ j<5,dst (a+1) j∉tblW := by decide
  have := h (a-1) (by omega_arith) j hj
  rwa [show a-1+1=a by omega_arith] at this

theorem dst_ne {a m j j' : Nat} (ha : 1≤a) (ha9 : a≤9) (hm : 1≤m) (hm9 : m≤9) (hj : j<5) (hj' : j'<5)
    (h : a≠m) : dst a j≠dst m j' := by
  have hh : ∀ a<9,∀ m<9,∀ j<5,∀ j'<5,dst (a+1) j=dst (m+1) j' → a=m := by decide
  intro he
  have := hh (a-1) (by omega_arith) (m-1) (by omega_arith) j hj j' hj'
    (by rwa [show a-1+1=a by omega_arith,show m-1+1=m by omega_arith])
  omega_arith

theorem not_dsts_of_ne {a m j : Nat} (ha : 1≤a) (ha9 : a≤9) (hm : 1≤m) (hm9 : m≤9) (hj : j<5)
    (h : a≠m) : dst a j∉dsts m := by
  simp only [dsts,List.mem_map,List.mem_range,not_exists,not_and]
  intro j' hj' he
  exact dst_ne ha ha9 hm hm9 hj hj' h he.symm

theorem w_not_dsts {m : Nat} (hm : 1≤m) (hm9 : m≤9) : ∀ x∈W,x∉dsts m := by
  have h : ∀ m<9,∀ x∈W,x∉dsts (m+1) := by decide
  have := h (m-1) (by omega_arith)
  rwa [show m-1+1=m by omega_arith] at this

theorem not_dvd_small {n : Nat} {x : Int} (h1 : -n<x) (h2 : x<n) (h0 : x≠0) : ¬ (n : Int)∣x := by
  rcases Int.lt_or_gt_of_ne h0 with h | h
  · intro hd
    exact not_dvd_of_pos_lt (n:=n) (x:=-x) (by omega_arith) (by omega_arith) (Int.dvd_neg.mpr hd)
  · exact not_dvd_of_pos_lt h h2

variable (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
include hC ha hO

omit ha in
/-- `(2k+1)Q` and `2Q` are neither equal nor opposite. -/
theorem coz_x {Q : Point C} (hQ : onCurve C Q=true) (hQ0 : Q≠.infinity) {k : Nat} (hk : k≤6)
    {X1 Y1 X2 Y2 Z : Fe C} (h1 : InvJ C X1 Y1 Z (mul 2 Q)) (h2 : InvJ C X2 Y2 Z (mul (2*k+1) Q))
    (hz : Z≠0) : X1-X2≠0 := by
  have hn : 17≤C.n := by decide
  intro hx
  have hx' : X1*(Z*Z)-X2*(Z*Z)=0 := by
    have e : X1*(Z*Z)-X2*(Z*Z)=(X1-X2)*(Z*Z) := by grind
    rw [e,hx]; grind
  by_cases hy : Y1*Z*(Z*Z)-Y2*Z*(Z*Z)=0
  · have he := h2.same hC h1 hz hz hx' hy
    have h' : zmul ((2*k+1 : Nat) : Int) Q=zmul (2 : Nat) Q := by
      rw [zmul_natCast,zmul_natCast,he]
    have hd := zmul_dvd hC hO hQ hQ0 h'
    exact not_dvd_small (n:=C.n) (x:=((2*k+1 : Nat) : Int)-(2 : Nat)) (by omega_arith) (by omega_arith) (by omega_arith) hd
  · have he := h2.opposite hC (hC.onCurve_mul hQ _) (hC.onCurve_mul hQ _) h1 hz hz hx' hy
    rw [hC.add_mul_mul hQ] at he
    exact mul_ne_infinity hO hQ hQ0 (m:=2*k+1+2) (by omega_arith) (by omega_arith) he

theorem coz_step {Q : Point C} (hQ : onCurve C Q=true) (hQ0 : Q≠.infinity) {k : Nat} (hk : k≤6)
    {F : Nat → Fe C} (h : CoZ Q k F) : CoZ Q (k+1) (stepEnv (k+2) F) := by
  have hn : 17≤C.n := by decide
  obtain ⟨ht,h11,h12⟩ := Proof.P256.EcdhJac.zadduN_run (fun j => F (tblσ j))
  have at' := fun i => ops_at false F i
  simp only [Bool.false_eq_true,↓reduceIte] at at'
  generalize runOps zadduN (fun j => F (tblσ j))=r at ht h11 h12 at'
  change ((r 8,r 9,r 10),(r 0,r 1))=zadduF (F 608) (F 640) (F 704) (F 736) (F 768) at ht
  change (F 5400=F 768*F 768 → r 11=r 10*r 10) at h11
  have hx := coz_x hC hO hQ hQ0 hk h.d h.e h.z
  obtain ⟨js,jd⟩ := InvJ.zaddu hC ha (hC.onCurve_mul hQ 2) (hC.onCurve_mul hQ _) h.d h.e h.z hx
  rw [hC.add_mul_mul hQ] at js
  rw [← ht] at js jd
  have js' : InvJ C (r 8) (r 9) (r 10) (mul (2*(k+1)+1) Q) := by
    rw [show 2*(k+1)+1=2*k+1+2 by omega_arith]; exact js
  have hz : r 10≠0 := fun hh => mul_ne_infinity hO hQ hQ0 (m:=2*(k+1)+1) (by omega_arith) (by omega_arith)
    ((js'.z_zero_iff hC).mp hh)
  -- The ZADDU environment `G` at the co-Z slots.
  have g : ∀ i<13,runOps (ops false) F (tblσ i)=r i := fun i _ => at' i
  have g0 : runOps (ops false) F 608=r 0 := g 0 (by decide)
  have g1 : runOps (ops false) F 640=r 1 := g 1 (by decide)
  have g8 : runOps (ops false) F 704=r 8 := g 8 (by decide)
  have g9 : runOps (ops false) F 736=r 9 := g 9 (by decide)
  have g10 : runOps (ops false) F 768=r 10 := g 10 (by decide)
  have g11 : runOps (ops false) F 5400=r 11 := g 11 (by decide)
  have g12 : runOps (ops false) F 5432=r 12 := g 12 (by decide)
  have hm1 : 1≤k+2 := by omega_arith
  have hm9 : k+2≤9 := by omega_arith
  have so (x : Nat) (hx : x∈W) : stepEnv (k+2) F x=runOps (ops false) F x :=
    storeEnv_other _ (w_not_dsts hm1 hm9 x hx)
  have sd (j : Nat) (hj : j<5) : stepEnv (k+2) F (dst (k+2) j)=runOps (ops false) F (src j) :=
    storeEnv_dst _ hj
  have old (a j : Nat) (ha1 : 1≤a) (hak : a≤k+1) (hj : j<5) :
      stepEnv (k+2) F (dst a j)=F (dst a j) := by
    unfold stepEnv
    rw [storeEnv_other _ (not_dsts_of_ne ha1 (by omega_arith) hm1 hm9 hj (by omega_arith)),
      ops_keep false F (dst_tblW ha1 (by omega_arith) hj)]
  have s0 := so 608 (by decide); have s1 := so 640 (by decide); have s8 := so 704 (by decide)
  have s9 := so 736 (by decide); have s10 := so 768 (by decide); have s11 := so 5400 (by decide)
  have s12 := so 5432 (by decide)
  have e0 := sd 0 (by decide); have e1 := sd 1 (by decide); have e2 := sd 2 (by decide)
  have e3 := sd 3 (by decide); have e4 := sd 4 (by decide)
  simp only [src,Nat.reduceLT,↓reduceIte,Nat.reduceSub,Nat.reduceMul,Nat.reduceAdd] at e0 e1 e2 e3 e4
  rw [g8] at e0; rw [g9] at e1; rw [g10] at e2; rw [g11] at e3; rw [g12] at e4
  refine ⟨?_,?_,?_,?_,?_,fun a ha1 hak => ?_,fun a ha1 hak => ?_,fun a ha1 hak => ?_⟩
  · rw [s0,s1,s10,g0,g1,g10]; exact jd
  · rw [s8,s9,s10,g8,g9,g10]; exact js'
  · rw [s10,g10]; exact hz
  · rw [s11,s10,g11,g10]; exact h11 h.z2
  · rw [s12,s11,s10,g12,g11,g10]; exact h12
  · by_cases hl : a=k+2
    · subst hl
      rw [e0,e1,e2,show 2*(k+2)-1=2*(k+1)+1 by omega_arith]; exact js'
    · rw [old a 0 ha1 (by omega_arith) (by decide),old a 1 ha1 (by omega_arith) (by decide),
        old a 2 ha1 (by omega_arith) (by decide)]
      exact h.tbl a ha1 (by omega_arith)
  · by_cases hl : a=k+2
    · subst hl; rw [e3,e2]; exact h11 h.z2
    · rw [old a 3 ha1 (by omega_arith) (by decide),old a 2 ha1 (by omega_arith) (by decide)]
      exact h.c2 a ha1 (by omega_arith)
  · by_cases hl : a=k+2
    · subst hl; rw [e4,e3,e2]; exact h12
    · rw [old a 4 ha1 (by omega_arith) (by decide),old a 3 ha1 (by omega_arith) (by decide),
        old a 2 ha1 (by omega_arith) (by decide)]
      exact h.c3 a ha1 (by omega_arith)

theorem coz_loop {Q : Point C} (hQ : onCurve C Q=true) (hQ0 : Q≠.infinity) {F : Nat → Fe C}
    (h : CoZ Q 0 F) : ∀ k≤7,CoZ Q k (loopEnv k F)
  | 0, _ => h
  | k+1, hk => coz_step hC ha hO hQ hQ0 (by omega_arith) (coz_loop hQ hQ0 h k (by omega_arith))

theorem coz_dblu {Q : Point C} (hQ : onCurve C Q=true) {E : Nat → Fe C}
    (jp : InvJ C (E 1280) (E 1440) 1 Q) (h1 : E 224=1) : CoZ Q 0 (dbluEnv E) := by
  have hn : 17≤C.n := by decide
  have hQ0 : Q≠.infinity := fun hh => hC.one_ne_zero ((jp.z_zero_iff hC).mpr hh)
  -- The start's environment.
  have st (x : Nat) (hx : x∈[1280,1440,224]) : startEnv E x=E x := by
    unfold startEnv
    rw [storeEnv_other _ (by revert x; decide),copiesEnv_keep _ _ (by revert x; decide)]
  have sd (j : Nat) (hj : j<5) : startEnv E (dst 1 j)=copiesEnv l1 E (src j) := storeEnv_dst _ hj
  have c1 : ∀ j<5,copiesEnv l1 E (src j)=[E 1280,E 1440,E 224,E 224,E 224].getD j 0 := by
    intro j hj
    have : j=0∨j=1∨j=2∨j=3∨j=4 := by omega_arith
    rcases this with rfl|rfl|rfl|rfl|rfl <;>
      simp only [copiesEnv,l1,src,Function.update_apply,Nat.reduceEqDiff,Nat.reduceLT,↓reduceIte,
        Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,List.getD_cons_zero,List.getD_cons_succ]
  obtain ⟨hT,h11,h12,h5,h4⟩ := Proof.P256.EcdhJac.dbluN_run (fun j => startEnv E (tblσ j))
    (st 224 (by decide) |>.trans h1)
  have at' := fun i => ops_at true (startEnv E) i
  simp only [↓reduceIte] at at'
  generalize runOps dbluN (fun j => startEnv E (tblσ j))=r at hT h11 h12 h5 h4 at'
  change (r 8,r 9,r 10)=dblJF (startEnv E 1280) (startEnv E 1440) 1 at hT
  rw [st 1280 (by decide),st 1440 (by decide)] at hT
  change r 5*(1*1)=startEnv E 1280*(r 10*r 10) at h5
  change r 4*(1*1*1)=startEnv E 1440*(r 10*r 10*r 10) at h4
  rw [st 1280 (by decide)] at h5
  rw [st 1440 (by decide)] at h4
  have j2 := InvJ.dbl' hC ha hQ jp hT
  rw [show add Q Q=mul 2 Q by
    rw [show add Q Q=add (mul 1 Q) (mul 1 Q) by rw [mul_one_pt],hC.add_mul_mul hQ]] at j2
  have hz : r 10≠0 := fun hh => mul_ne_infinity hO hQ hQ0 (m:=2) (by decide) (by omega_arith)
    ((j2.z_zero_iff hC).mp hh)
  have jd : InvJ C (r 5) (r 4) (r 10) Q := jp.rescale hC hz hC.one_ne_zero h5 h4 (by grind only)
  have g (i : Nat) (hi : i<13) : runOps (ops true) (startEnv E) (tblσ i)=r i := at' i
  -- After the swap.
  have sw : ∀ x,dbluEnv E x=copiesEnv l2 (runOps (ops true) (startEnv E)) x := fun _ => rfl
  have w0 : dbluEnv E 608=r 8 := by
    rw [sw]; simp only [copiesEnv,l2,Function.update_apply,Nat.reduceEqDiff,↓reduceIte]
    exact g 8 (by decide)
  have w1 : dbluEnv E 640=r 9 := by
    rw [sw]; simp only [copiesEnv,l2,Function.update_apply,Nat.reduceEqDiff,↓reduceIte]
    exact g 9 (by decide)
  have w8 : dbluEnv E 704=r 5 := by
    rw [sw]; simp only [copiesEnv,l2,Function.update_apply,Nat.reduceEqDiff,↓reduceIte]
    exact g 5 (by decide)
  have w9 : dbluEnv E 736=r 4 := by
    rw [sw]; simp only [copiesEnv,l2,Function.update_apply,Nat.reduceEqDiff,↓reduceIte]
    exact g 4 (by decide)
  have wk (x : Nat) (hx : x∉l2.map Prod.fst) : dbluEnv E x=runOps (ops true) (startEnv E) x :=
    copiesEnv_keep _ _ hx
  have w10 : dbluEnv E 768=r 10 := (wk 768 (by decide)).trans (g 10 (by decide))
  have w11 : dbluEnv E 5400=r 11 := (wk 5400 (by decide)).trans (g 11 (by decide))
  have w12 : dbluEnv E 5432=r 12 := (wk 5432 (by decide)).trans (g 12 (by decide))
  have ent (j : Nat) (hj : j<5) : dbluEnv E (dst 1 j)=copiesEnv l1 E (src j) := by
    rw [wk _ (by revert j; decide),ops_keep true _ (dst_tblW (by decide) (by decide) hj),sd j hj]
  have n0 := ent 0 (by decide); have n1 := ent 1 (by decide); have n2 := ent 2 (by decide)
  have n3 := ent 3 (by decide); have n4 := ent 4 (by decide)
  rw [c1 0 (by decide)] at n0; rw [c1 1 (by decide)] at n1; rw [c1 2 (by decide)] at n2
  rw [c1 3 (by decide)] at n3; rw [c1 4 (by decide)] at n4
  simp only [List.getD_cons_zero,List.getD_cons_succ,h1] at n0 n1 n2 n3 n4
  refine ⟨?_,?_,?_,?_,?_,fun a ha1 hak => ?_,fun a ha1 hak => ?_,fun a ha1 hak => ?_⟩
  · rw [w0,w1,w10]; exact j2
  · rw [w8,w9,w10,show 2*0+1=1 from rfl,mul_one_pt]; exact jd
  · rw [w10]; exact hz
  · rw [w11,w10]; exact h11
  · rw [w12,w11,w10]; exact h12
  · obtain rfl : a=1 := by omega_arith
    rw [n0,n1,n2,show 2*1-1=1 from rfl,mul_one_pt]; exact jp
  · obtain rfl : a=1 := by omega_arith
    rw [n3,n2]; grind
  · obtain rfl : a=1 := by omega_arith
    rw [n4,n3,n2]; grind

/-- The build's values: entry `a` is `(2a-1)Q`, with its cached powers. -/
theorem build_env {Q : Point C} (hQ : onCurve C Q=true) {E : Nat → Fe C}
    (jp : InvJ C (E 1280) (E 1440) 1 Q) (h1 : E 224=1) :
    ∀ a,1≤a → a≤8 →
      InvJ C (buildEnv E (dst a 0)) (buildEnv E (dst a 1)) (buildEnv E (dst a 2)) (mul (2*a-1) Q) ∧
      buildEnv E (dst a 3)=buildEnv E (dst a 2)*buildEnv E (dst a 2) ∧
      buildEnv E (dst a 4)=buildEnv E (dst a 3)*buildEnv E (dst a 2) := by
  have hQ0 : Q≠.infinity := fun hh => hC.one_ne_zero ((jp.z_zero_iff hC).mpr hh)
  have h := coz_loop hC ha hO hQ hQ0 (coz_dblu hC ha hO hQ jp h1) 7 (by decide)
  intro a ha1 ha8
  have k (j : Nat) (hj : j<5) : buildEnv E (dst a j)=loopEnv 7 (dbluEnv E) (dst a j) := by
    apply copiesEnv_keep
    have hh : ∀ a<8,∀ j<5,dst (a+1) j∉l4.map Prod.fst := by decide
    have := hh (a-1) (by omega_arith) j hj
    rwa [show a-1+1=a by omega_arith] at this
  rw [k 0 (by decide),k 1 (by decide),k 2 (by decide),k 3 (by decide),k 4 (by decide)]
  exact ⟨h.tbl a ha1 (by omega_arith),h.c2 a ha1 (by omega_arith),h.c3 a ha1 (by omega_arith)⟩

end VG.Proof.P256.VerifyTable
