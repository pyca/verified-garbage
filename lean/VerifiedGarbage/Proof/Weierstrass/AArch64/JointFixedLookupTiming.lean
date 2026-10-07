import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

def jointAffineCoords {C : Curve} : Point C → Fe C × Fe C
  | .infinity => (0,0)
  | .affine x y => (x,y)

theorem jointAffine_unique {C : Curve} (hC : Law C) {X Y : Fe C} {P : Point C}
    (h : InvJ C X Y 1 P) : (X,Y)=jointAffineCoords P := by
  rcases h with ⟨_,hz⟩ | h
  · exact False.elim (hC.one_ne_zero hz)
  · simp only [Lean.Grind.Semiring.mul_one] at h
    cases P with
    | infinity => exact False.elim (hC.one_ne_zero h.2.2)
    | affine x y =>
      apply Prod.ext
      · simpa only [Lean.Grind.Semiring.mul_one,jointAffineCoords] using h.2.1
      · simpa only [Lean.Grind.Semiring.mul_one,jointAffineCoords] using h.2.2

theorem jointFieldWrite_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V V' W : List Nat} {E F : Nat → Fin m}
    {code : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hct : ConstantTime isa (fun _ => True) Pub code)
    (hpub : ∀ s t,FieldPair M base size m Sl V E s t → Pre s → Pre t → Pub s t)
    (hW : ∀ x∈W,Sl x) (hV : ∀ x∈V',x∈W ∨ x∈V)
    (hw : ∀ s,Inv M base size m Sl V E s → Pre s → WP isa code s fun t =>
      ∃ E',ProgKeep M base W s t ∧ Inv M base size m Sl V' E' t ∧
        ∀ x∈V',x∈W → E' x=F x) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) code
      (fun s t => ∃ E',FieldPair M base size m Sl V' E' s t) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨_,_,xs,Es,ks,is,vs⟩ := hw s hp.left ps
  obtain ⟨_,_,xt,Et,kt,it,vt⟩ := hw t hp.right pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp ps pt) es et,Es,?_⟩
  exact hp.rebuild hL ks kt hW is it hV (fun x hx hw => (vs x hx hw).trans (vt x hx hw).symm)

theorem jointLookup_relCT {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {E : Nat → Fe C} (hL : JointFixedLayout c size) (hC : Law C)
    (hm0 : FastNaf.magnitude 7 u j≠0) (hc : JointFixedChecks c) :
    RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      (JointCore c C base size Q u v (JointGenerator c C base size G T) A s ∧
        s.gpr .x2=(FastNaf.byte 7 u j).setWidth 64) ∧
      (JointCore c C base size Q u v (JointGenerator c C base size G T) A t ∧
        t.gpr .x2=(FastNaf.byte 7 u j).setWidth 64))
      (.block (Naf.digitIndex++Joint.fixedLoad c))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c)
        ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) E' s t) := by
  let P := mul (FastNaf.magnitude 7 u j) G
  let F := fun x => if x=c.K.E.x then (jointAffineCoords P).1 else
    if x=c.K.E.y then (jointAffineCoords P).2 else 1
  apply jointFieldWrite_relCT (F:=F) hL.layout.lay hc.lookup
  · intro s t hp ps pt
    refine ⟨⟨hp.sp,fun r hr => ?_⟩,?_⟩
    · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.2.trans pt.2.symm
    · intro n hn; rw [List.mem_singleton.mp hn]
      exact ps.1.external.symbol.trans pt.1.external.symbol.symm
  · exact jointEntry_slots c
  · intro x hx; exact List.mem_append.mp hx
  · intro s _ hs
    refine WP.mono (jointLookup_generator_ok hL hs.1 hs.2 hm0) fun t ⟨kt,_,it,jt,zt⟩ => ⟨_,kt,it,?_⟩
    rw [zt] at jt
    have he := jointAffine_unique hC jt
    have hex := congrArg Prod.fst he
    have hey := congrArg Prod.snd he
    have hn := hL.entryNodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    intro x _ hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F,ite_true] using hex
    · simpa only [F,Ne.symm hn.1.1,ite_false,ite_true] using hey
    · simpa only [F,Ne.symm hn.1.2,Ne.symm hn.2.1,ite_false] using zt

end VG.Proof.Weierstrass.AArch64
