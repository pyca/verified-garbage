import VerifiedGarbage.Impl.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.Jac

namespace VG.Proof.Weierstrass
open Spec.Weierstrass

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- Jacobian addition for distinct affine x coordinates. -/
def jacAddF (X1 Y1 Z1 X2 Y2 Z2 : F) : F × F × F :=
  let u1 := X1 * (Z2 * Z2)
  let u2 := X2 * (Z1 * Z1)
  let s1 := Y1 * Z2 * (Z2 * Z2)
  let s2 := Y2 * Z1 * (Z1 * Z1)
  let h := u2-u1
  let r := s2-s1
  let hh := h*h
  let hhh := hh*h
  let v := u1*hh
  let x := r*r-hhh-v-v
  let y := r*(v-x)-s1*hhh
  (x,y,Z1*Z2*h)

/-- The Jacobian and complete projective formulas give proportional coordinates. -/
theorem jacAddF_cross (b X1 Y1 Z1 X2 Y2 Z2 : F)
    (h1 : Y1*Y1 = X1*X1*X1-3*X1*Z1*Z1*Z1*Z1+b*Z1*Z1*Z1*Z1*Z1*Z1)
    (h2 : Y2*Y2 = X2*X2*X2-3*X2*Z2*Z2*Z2*Z2+b*Z2*Z2*Z2*Z2*Z2*Z2) :
    let j := jacAddF X1 Y1 Z1 X2 Y2 Z2
    let p := rcbAdd3 b (X1*Z1) Y1 (Z1*Z1*Z1) (X2*Z2) Y2 (Z2*Z2*Z2)
    (j.1*j.2.2)*p.2.2 = p.1*(j.2.2*j.2.2*j.2.2) ∧
      j.2.1*p.2.2 = p.2.1*(j.2.2*j.2.2*j.2.2) := by
  dsimp only [jacAddF,rcbAdd3]
  constructor <;> grind

end

variable {C : Curve}

theorem cancel_right (hC : Law C) {a b z : Fe C} (hz : z ≠ 0) (h : a*z = b*z) : a=b := by
  by_contra hn
  have hn' : a-b ≠ 0 := fun he => hn (by grind)
  exact hC.mul_ne_zero hn' hz (by grind)

theorem InvJ.rep_of_ne {X Y Z : Fe C} {Q : Point C} (h : InvJ C X Y Z Q) (hz : Z ≠ 0) :
    Rep C (X*Z) Y (Z*Z*Z) Q := by
  rcases h with ⟨_,h0⟩ | h
  · exact False.elim (hz h0)
  · exact h

theorem InvJ.curve (hC : Law C) (ha : AM3 C) {X Y Z : Fe C} {Q : Point C}
    (h : InvJ C X Y Z Q) (hz : Z ≠ 0) (hQ : onCurve C Q = true) :
    Y*Y = X*X*X-3*X*Z*Z*Z*Z+Fin.ofNat C.p C.b*Z*Z*Z*Z*Z*Z := by
  have e := (h.rep_of_ne hz).proj hQ
  rw [ha] at e
  apply cancel_right hC (cube_ne_zero hC hz)
  grind

theorem Rep.of_cross (hC : Law C) {X Y Z A B D : Fe C} {Q : Point C}
    (h : Rep C A B D Q) (hz : Z ≠ 0) (hx : X*D=A*Z) (hy : Y*D=B*Z) :
    Rep C X Y Z Q := by
  cases Q with
  | infinity =>
    obtain ⟨_,hb,hd⟩ := h
    exact False.elim (hC.mul_ne_zero hb hz (by rw [hd] at hy; grind))
  | affine x y =>
    obtain ⟨hd,ha,hb⟩ := h
    refine ⟨hz,cancel_right hC hd ?_,cancel_right hC hd ?_⟩ <;> grind

theorem InvJ.add_ne (hC : Law C) (ha : AM3 C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q)
    (hz1 : Z1 ≠ 0) (hz2 : Z2 ≠ 0) (hh : X2*(Z1*Z1)-X1*(Z2*Z2) ≠ 0) :
    let j := jacAddF X1 Y1 Z1 X2 Y2 Z2
    InvJ C j.1 j.2.1 j.2.2 (Spec.Weierstrass.add P Q) := by
  let j := jacAddF X1 Y1 Z1 X2 Y2 Z2
  let r := rcbAdd3 (Fin.ofNat C.p C.b) (X1*Z1) Y1 (Z1*Z1*Z1) (X2*Z2) Y2 (Z2*Z2*Z2)
  have hr : Rep C r.1 r.2.1 r.2.2 (Spec.Weierstrass.add P Q) :=
    hC.add3 ha hP hQ (h1.rep_of_ne hz1) (h2.rep_of_ne hz2) rfl
  have hjz : j.2.2 ≠ 0 := hC.mul_ne_zero (hC.mul_ne_zero hz1 hz2) hh
  have cross := jacAddF_cross (Fin.ofNat C.p C.b) X1 Y1 Z1 X2 Y2 Z2
    (h1.curve hC ha hz1 hP) (h2.curve hC ha hz2 hQ)
  exact Or.inr (hr.of_cross hC (cube_ne_zero hC hjz) cross.1 cross.2)

theorem InvJ.z_zero_iff (hC : Law C) {X Y Z : Fe C} {P : Point C}
    (h : InvJ C X Y Z P) : Z=0 ↔ P=.infinity := by
  rcases h with ⟨hp,hz⟩ | h
  · simp only [hp,hz]
  · constructor
    · intro hz; exact h.z_eq_zero_iff.mp (by rw [hz]; grind)
    · intro hp
      have he := h.z_eq_zero_iff.mpr hp
      by_contra hn
      exact cube_ne_zero hC hn he

theorem InvJ.affine_coords (hC : Law C) {X Y Z x y : Fe C}
    (h : InvJ C X Y Z (.affine x y)) : X=x*(Z*Z) ∧ Y=y*(Z*Z*Z) := by
  have hz : Z ≠ 0 := by
    intro he
    have bad := (h.z_zero_iff hC).mp he
    cases bad
  obtain ⟨_,hx,hy⟩ := h.rep_of_ne hz
  exact ⟨cancel_right hC hz (by grind),hy⟩

theorem InvJ.same (hC : Law C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q)
    (hz1 : Z1 ≠ 0) (hz2 : Z2 ≠ 0)
    (hx : X2*(Z1*Z1)-X1*(Z2*Z2)=0)
    (hy : Y2*Z1*(Z1*Z1)-Y1*Z2*(Z2*Z2)=0) : P=Q := by
  cases P with
  | infinity => exact False.elim (hz1 ((h1.z_zero_iff hC).mpr rfl))
  | affine x1 y1 =>
    cases Q with
    | infinity => exact False.elim (hz2 ((h2.z_zero_iff hC).mpr rfl))
    | affine x2 y2 =>
      obtain ⟨a1,b1⟩ := h1.affine_coords hC
      obtain ⟨a2,b2⟩ := h2.affine_coords hC
      have ex : x1=x2 := cancel_right hC
        (hC.mul_ne_zero (hC.mul_ne_zero hz1 hz1) (hC.mul_ne_zero hz2 hz2)) (by grind)
      have ey : y1=y2 := cancel_right hC
        (hC.mul_ne_zero (cube_ne_zero hC hz1) (cube_ne_zero hC hz2)) (by grind)
      rw [ex,ey]

theorem InvJ.opposite (hC : Law C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q)
    (hz1 : Z1 ≠ 0) (hz2 : Z2 ≠ 0)
    (hx : X2*(Z1*Z1)-X1*(Z2*Z2)=0)
    (hy : Y2*Z1*(Z1*Z1)-Y1*Z2*(Z2*Z2)≠0) : Spec.Weierstrass.add P Q=.infinity := by
  cases P with
  | infinity => exact False.elim (hz1 ((h1.z_zero_iff hC).mpr rfl))
  | affine x1 y1 =>
    cases Q with
    | infinity => exact False.elim (hz2 ((h2.z_zero_iff hC).mpr rfl))
    | affine x2 y2 =>
      obtain ⟨a1,b1⟩ := h1.affine_coords hC
      obtain ⟨a2,b2⟩ := h2.affine_coords hC
      have ex : x1=x2 := cancel_right hC
        (hC.mul_ne_zero (hC.mul_ne_zero hz1 hz1) (hC.mul_ne_zero hz2 hz2)) (by grind)
      have ey : y2-y1 ≠ 0 := fun he => hy (by grind)
      simp only [onCurve,decide_eq_true_eq] at hP hQ
      have en : y2+y1=0 := by
        by_contra hn
        exact hC.mul_ne_zero ey hn (by grind)
      have eyn : y2 = -y1 := by grind
      simp only [Spec.Weierstrass.add,ex,eyn,↓reduceIte,and_self]

/-- Complete public-data Jacobian addition, including infinity and equal x coordinates. -/
def jacAddComplete (X1 Y1 Z1 X2 Y2 Z2 : Fe C) : Fe C × Fe C × Fe C :=
  if Z1 = 0 then (X2,Y2,Z2)
  else if Z2 = 0 then (X1,Y1,Z1)
  else if X2*(Z1*Z1)-X1*(Z2*Z2) = 0 then
    if Y2*Z1*(Z1*Z1)-Y1*Z2*(Z2*Z2) = 0 then dblJF X1 Y1 Z1
    else (0,1,0)
  else jacAddF X1 Y1 Z1 X2 Y2 Z2

theorem InvJ.add (hC : Law C) (ha : AM3 C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q) :
    let j := jacAddComplete X1 Y1 Z1 X2 Y2 Z2
    InvJ C j.1 j.2.1 j.2.2 (Spec.Weierstrass.add P Q) := by
  dsimp only [jacAddComplete]
  split
  next hz =>
    rw [(h1.z_zero_iff hC).mp hz]
    exact h2
  next hz1 =>
    split
    next hz =>
      rw [(h2.z_zero_iff hC).mp hz]
      cases P <;> exact h1
    next hz2 =>
      split
      next hx =>
        split
        next hy =>
          rw [← h1.same hC h2 hz1 hz2 hx hy]
          exact h1.dbl hC ha hP
        next hy =>
          exact Or.inl ⟨h1.opposite hC hP hQ h2 hz1 hz2 hx hy,rfl⟩
      next hx => exact h1.add_ne hC ha hP hQ h2 hz1 hz2 hx

open VG.Impl.Weierstrass

def jacHeadN : List FOp := jacHead ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨14,15,16⟩
def jacTailN : List FOp := jacTail ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨14,15,16⟩ ⟨6,7,8⟩

theorem jacAddN_ok : NumOk (jacHeadN ++ jacTailN) := ⟨by decide,by decide,by decide⟩

def jacAddSN : List FOp := jacAddS ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨14,15,16⟩ ⟨6,7,8⟩

theorem jacAddSN_ok : NumOk jacAddSN := ⟨by decide,by decide,by decide⟩

theorem jacAddS_eq (S : RcbSlots) (p q o : Pt) : jacAddS S p q o = ofN jacAddSN S p q o := rfl

theorem jacAddSN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    let r := runOps jacAddSN e
    (r 6,r 7,r 8) = jacAddF (e 11) (e 12) (e 13) (e 14) (e 15) (e 16) := by
  dsimp only [jacAddSN, jacAddS, runOps, List.foldl, FOp.run, Function.update]
  simp only [jacAddF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem jacHead_eq (S : RcbSlots) (p q o : Pt) :
    jacHead S p q = ofN jacHeadN S p q o := rfl

theorem jacTail_eq (S : RcbSlots) (p q o : Pt) :
    jacTail S p q o = ofN jacTailN S p q o := rfl

theorem jacHeadN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    let r := runOps jacHeadN e
    r 2 = e 11 * (e 16 * e 16) ∧
    r 3 = e 14 * (e 13 * e 13) - e 11 * (e 16 * e 16) ∧
    r 4 = e 12 * e 16 * (e 16 * e 16) ∧
    r 5 = e 15 * e 13 * (e 13 * e 13) - e 12 * e 16 * (e 16 * e 16) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem jacAddN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    let r := runOps (jacHeadN ++ jacTailN) e
    (r 6,r 7,r 8) = jacAddF (e 11) (e 12) (e 13) (e 14) (e 15) (e 16) := rfl

/-- An affine point is already a Jacobian representative with z coordinate one. -/
theorem InvJ.affine (hC : Law C) (x y : Fe C) : InvJ C x y 1 (.affine x y) := by
  right
  show (1:Fe C)*1*1 ≠ 0 ∧ x*1=x*(1*1*1) ∧ y=y*(1*1*1)
  simp only [Lean.Grind.Semiring.mul_one]
  exact ⟨hC.one_ne_zero, trivial, trivial⟩

/-- Reflecting a Jacobian representative only negates its y coordinate. -/
theorem InvJ.negY {X Y Z : Fe C} {P : Point C} (h : InvJ C X Y Z P) :
    InvJ C X (-Y) Z (negPt P) := by
  rcases h with ⟨rfl,hz⟩ | h
  · exact Or.inl ⟨rfl,hz⟩
  · exact Or.inr h.negY

def jacMixedHeadN : List FOp := jacMixedHead ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨14,15,16⟩
def jacMixedTailN : List FOp := jacMixedTail ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨14,15,16⟩ ⟨6,7,8⟩

/-- Copying to the two header temporaries, as the machine's copy blocks do. -/
def jacMixedEnv {F : Type _} (e : Nat → F) : Nat → F :=
  Function.update (Function.update e 2 (e 11)) 4 (e 12)

theorem jacMixedN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    let r := runOps (jacMixedHeadN ++ jacMixedTailN) (jacMixedEnv e)
    (r 6,r 7,r 8) = jacAddF (e 11) (e 12) (e 13) (e 14) (e 15) 1 := by
  simp only [jacAddF, Lean.Grind.Semiring.mul_one]
  rfl


/-- The mixed header's two initial copies. -/
def jacMixedInit {F : Type _} (S : RcbSlots) (p : Pt) (E : Nat → F) : Nat → F :=
  let E1 := Function.update E S.t2 (E p.x)
  Function.update E1 S.t4 (E1 p.y)

theorem update_rcbσ {F : Type _} {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (E : Nat → F) (v : F) {w : Nat} (hw : w < 9) :
    (fun i => Function.update E (rcbσ S p q o w) v (rcbσ S p q o i)) =
      Function.update (fun i => E (rcbσ S p q o i)) w v := by
  funext i
  by_cases hi : i = w
  · subst hi; simp only [Function.update_self]
  · have hn : rcbσ S p q o i ≠ rcbσ S p q o w := fun he => hi (hA.inj hw i he)
    rw [Function.update_of_ne hn,Function.update_of_ne hi]

theorem jacMixedInit_rename {F : Type _} {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (E : Nat → F) :
    (fun i => jacMixedInit S p E (rcbσ S p q o i)) = jacMixedEnv (fun i => E (rcbσ S p q o i)) := by
  have hy : p.y ≠ S.t2 := by
    intro he
    have hh := hA.inj (w := 2) (by decide) 12 he
    omega
  unfold jacMixedInit
  rw [Function.update_of_ne hy]
  change (fun i => Function.update (Function.update E (rcbσ S p q o 2) (E p.x))
    (rcbσ S p q o 4) (E p.y) (rcbσ S p q o i)) = _
  rw [update_rcbσ hA _ _ (by decide),update_rcbσ hA _ _ (by decide)]
  rfl

theorem jacMixedHead_eq (S : RcbSlots) (p q o : Pt) :
    jacMixedHead S p q = ofN jacMixedHeadN S p q o := rfl

theorem jacMixedTail_eq (S : RcbSlots) (p q o : Pt) :
    jacMixedTail S p q o = ofN jacMixedTailN S p q o := rfl

theorem jacMixedHeadN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    let r := runOps jacMixedHeadN (jacMixedEnv e)
    r 3 = e 14*(e 13*e 13)-e 11 ∧ r 5 = e 15*e 13*(e 13*e 13)-e 12 := ⟨rfl,rfl⟩


end VG.Proof.Weierstrass
