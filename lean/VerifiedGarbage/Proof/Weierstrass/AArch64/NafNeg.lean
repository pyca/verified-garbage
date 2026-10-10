import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowCore

/-! ## `NafCore` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Register-only instructions retain the arithmetic invariant. -/
theorem NafCore.of_keeps {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat} {β : Nat → BitVec 8}
    {P : Point C} {s t : State} {rs : List Reg} (h : NafCore K C base size P β e s)
    (hk : Keeps rs s t) (h0 : Reg.x0 ∉ rs) : NafCore K C base size P β e t := by
  have hm : tmv C K.M.n base t = tmv C K.M.n base s := by
    funext x; unfold tmv; rw [hk.mem]
  refine ⟨?_,?_,?_⟩
  · rw [hm]; exact h.field.of_keeps hk h0
  · refine ⟨?_,fun a ha h16 => ?_,fun i hi => ?_⟩
    · rw [hk.mem]; exact h.stable.zero
    · rw [hm]; exact h.stable.table a ha h16
    · rw [hk.mem]; exact h.stable.bits i hi
  · rw [hm]; exact h.point


theorem nafDoubleCore_ok {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat}
    {β : Nat → BitVec 8}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s : State} (h : NafCore K C base size P β e s) :
    WP isa (.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D))) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧ NafCore K C base size P β (2*e) t := by
  have old := hL.toWinLay hJ
  have sl (p o : Pt) (hp : p=K.R ∨ p=K.D) (ho : o=K.R ∨ o=K.D) :
      ∀ x∈rcbW K.S o ++ rcbR K.S p p,x∈jacWinSlots K := by
    intro x hx; apply hL.old_slots x
    rcases hp with rfl | rfl <;> rcases ho with rfl | rfl <;>
      simp only [rcbW,rcbR,winSlots,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  have vr (p : Pt) (hp : p=K.R ∨ p=K.D) : ∀ x∈rcbR K.S p p,x∈nafLive K := by
    intro x hx
    rcases hp with rfl | rfl <;>
      simp only [rcbR,nafLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  have ww (o : Pt) (ho : o=K.R ∨ o=K.D) : ∀ x∈rcbW K.S o,x∈winOther K := by
    intro x hx
    rcases ho with rfl | rfl <;>
      simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  apply WP.seq
  refine WP.mono (Forward.double_multiple_ok Forward.Production.cases (W:=winOther K) hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm hC ha
    (old.rcbApart_D (Or.inl rfl)) (sl _ _ (Or.inl rfl) (Or.inr rfl))
    (ww _ (Or.inr rfl)) h.field (vr _ (Or.inl rfl)) hP h.point) fun t ⟨E,kt,it,jt⟩ => ?_
  rw [←hL.n]
  refine WP.mono (copyPoint_ok hL.lay hAl hL.rcbApart_DR
    (sl _ _ (Or.inr rfl) (Or.inl rfl)) it (vr _ (Or.inr rfl))) fun u ⟨E',ku,iu,hu⟩ => ?_
  have kp := kt.trans (ku.mono (ww _ (Or.inl rfl)))
  refine ⟨kp,h.next hL hJ kp (iu.sub (fun _ hx => List.mem_append_right _ hx)) ?_⟩
  simp only [Prod.mk.injEq] at hu
  rw [hu.1,hu.2.1,hu.2.2]
  exact jt

/-- Work-slot writes disjoint from R preserve the accumulator and stable tables. -/
theorem NafCore.of_write {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat}
    {β : Nat → BitVec 8} {P : Point C} {s t : State} {W : List Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (h : NafCore K C base size P β e s)
    (hk : ProgKeep K.M base W s t) (hw : ∀ x∈W,x∈winOther K)
    (hn : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉W)
    (hi : Inv K.M base size C.p (·∈jacWinSlots K) (nafLive K) (tmv C K.M.n base t) t) :
    NafCore K C base size P β e t := by
  have hr : ∀ x∈[K.R.x,K.R.y,K.R.z],x∈jacWinSlots K := by
    intro x hx; exact h.field.sl x (nafLive_R K x hx)
  refine ⟨hi,h.stable.keep hL hJ h.field.scr.nowrap (hk.mono hw).unch,?_⟩
  apply point_of_unch hL h.field.scr.nowrap hk hr _ h.point
  intro x hx y hy
  apply hL.lay.apart x y (hr x hx) (List.mem_append_left _ (List.mem_append_right _ (hw y hy))) (fun he => hn x hx (he ▸ hy))

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafNeg` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem nafNeg_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈[K.E.x,K.E.y,K.E.z,K.zero],x∈V)
    (hxy : K.E.x≠K.E.y) (hzy : K.E.z≠K.E.y) (hz : E K.zero=0)
    {P : Point C} (hp : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) P) :
    WP isa (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y)) s fun t =>
      ProgKeep K.M base [K.E.y] s t ∧
      Inv K.M base size C.p Sl V (Function.update E K.E.y (-E K.E.y)) t ∧
      InvJ C ((Function.update E K.E.y (-E K.E.y)) K.E.x)
        ((Function.update E K.E.y (-E K.E.y)) K.E.y)
        ((Function.update E K.E.y (-E K.E.y)) K.E.z) (negPt P) := by
  have hs : ∀ x∈(FOp.sub K.E.y K.zero K.E.y).out::(FOp.sub K.E.y K.zero K.E.y).ins,Sl x := by
    intro x hx; apply hi.sl x; apply hV x
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hv : ∀ x∈(FOp.sub K.E.y K.zero K.E.y).ins,x∈V := by
    intro x hx; apply hV x
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono (fop_ok hL hAl hm hi hs hv) fun t ⟨kt,it⟩ => ?_
  have he : FOp.run (.sub K.E.y K.zero K.E.y) E=Function.update E K.E.y (-E K.E.y) := by
    simp only [FOp.run,hz]; congr 1
  rw [he] at it
  refine ⟨progKeep_of_op kt (by simp [FOp.out]),it.sub (fun _ hx => List.mem_cons_of_mem _ hx),?_⟩
  simpa only [Function.update_of_ne hxy,Function.update_of_ne hzy,Function.update_self] using hp.negY

end VG.Proof.Weierstrass.AArch64

end
