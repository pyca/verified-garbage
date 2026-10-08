import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.Ladder

/-! Field environments and point preservation for public Jacobian loops. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

/-- A multiple-slot update can reconstruct its environment from the resulting
memory. Bounds on changed slots and the frame preserve every initialized slot. -/
theorem Inv.of_progKeep {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAcc : WkOk F M m size wk Sl) {V W : List Nat}
    {E : Nat → Fin m} {s t : State} (hI : Inv M base size m Sl V E s)
    (hk : ProgKeep M base wk W s t) (hW : ∀ x ∈ W, Sl x)
    (hlt : ∀ x ∈ W, wordsVal t.mem base x M.n < m) :
    Inv M base size m Sl (W++V)
      (fun x => toM m (2^(64*M.n)) (wordsVal t.mem base x M.n)) t := by
  have hM := hI.mod
  refine ⟨hk.scr hI.scr,⟨hM.n0,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red⟩,?_,?_,fun _ _ => rfl⟩
  · rw [hk.wordsVal hI.scr.nowrap hM.mo (fun w hw => (hL.mo w (hW w hw)).symm)
      hM.sep hAcc.mo (by have := hAcc.toCallCfg.own_le; have := hAcc.mo; omega)]
    exact hM.val
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hW x hx
    · exact hI.sl x hx
  · intro x hx
    by_cases hw : x∈W
    · exact hlt x hw
    · have hv := (List.mem_append.mp hx).resolve_left hw
      have sl := hI.sl x hv
      rw [hk.wordsVal hI.scr.nowrap (hL.le x sl)
        (fun y hy => hL.apart x y sl (hW y hy) (fun he => hw (he ▸ hy)))
        (hL.tmp x sl) (hAcc.sl x sl) (by have := hAcc.toCallCfg.own_le; have := hAcc.sl x sl; omega)]
      exact hI.lt x hv


def jacCoords (p : Pt) : List Nat := [p.x,p.y,p.z]

theorem ProgKeep.slot {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size wk m : Nat} {Sl : Nat → Prop}
    {s t : State} {W : List Nat} (hL : Lay M size Sl) (hAcc : WkOk F M m size wk Sl) (hs : Scr s base size)
    (hk : ProgKeep M base wk W s t) (hW : ∀ x∈W, Sl x) {x : Nat}
    (hx : Sl x) (hn : x∉W) : VG.Proof.Mont.wordsVal t.mem base x M.n=VG.Proof.Mont.wordsVal s.mem base x M.n := by
  exact hk.wordsVal hs.nowrap (hL.le x hx)
    (fun y hy => hL.apart x y hx (hW y hy) (fun he => hn (he ▸ hy)))
    (hL.tmp x hx) (hAcc.sl x hx) (by have := hAcc.toCallCfg.own_le; have := hAcc.sl x hx; omega)

/-- An initialized environment can always be represented by the current
memory function, avoiding artificial relationships between temporary environments. -/
theorem Inv.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) : Inv M base size C.p Sl V (tmv C M.n base s) s :=
  ⟨h.scr,h.mod,h.sl,h.lt,fun _ _ => rfl⟩

theorem Inv.point_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) {p : Pt} {P : Point C}
    (hp : ∀ x ∈ [p.x,p.y,p.z], x ∈ V) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P := by
  unfold tmv
  rw [h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp))]
  exact hJ


theorem copyPointFields_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAcc : WkOk F M m size wk Sl)
    {q o : Pt} (hN : (jacCoords o).Nodup)
    (hqa : ∀ x∈jacCoords q, ∀ y∈jacCoords o, x≠y)
    (hO : ∀ x∈jacCoords o, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x∈jacCoords q, x∈V) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ∃ E', ProgKeep M base wk (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o ++ V) E' t ∧
      (E' o.x,E' o.y,E' o.z)=(E q.x,E q.y,E q.z) := by
  have hn := hN
  simp only [jacCoords,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  have hox := hO o.x (by simp [jacCoords])
  have hoy := hO o.y (by simp [jacCoords])
  have hoz := hO o.z (by simp [jacCoords])
  have hqx := hV q.x (by simp [jacCoords])
  have hqy := hV q.y (by simp [jacCoords])
  have hqz := hV q.z (by simp [jacCoords])
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAcc hI hox hqx) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAcc ia hoy (List.mem_cons_of_mem _ hqy)) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAcc ib hoz
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hqz))) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [jacCoords])).trans
    ((progKeep_of_op kb (by simp [jacCoords])).trans (progKeep_of_op kt (by simp [jacCoords]))),
    it.sub ?_,?_⟩
  · intro x hx
    simp only [jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · simp only [Function.update_self,Function.update_of_ne hn.1.1,
      Function.update_of_ne hn.1.2,Function.update_of_ne hn.2.1,
      Function.update_of_ne (hqa q.y (by simp [jacCoords]) o.x (by simp [jacCoords])),
      Function.update_of_ne (hqa q.z (by simp [jacCoords]) o.x (by simp [jacCoords])),
      Function.update_of_ne (hqa q.z (by simp [jacCoords]) o.y (by simp [jacCoords]))]

theorem ProgKeep.invJ {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size wk : Nat} {C : Curve}
    {Sl : Nat → Prop} {s t : State} {W : List Nat} (hL : Lay M size Sl) (hAcc : WkOk F M C.p size wk Sl) (hs : Scr s base size)
    (hk : ProgKeep M base wk W s t) (hW : ∀ x∈W, Sl x) {p : Pt}
    (hp : ∀ x∈jacCoords p, Sl x) (hDisj : ∀ x∈jacCoords p, x∉W) {P : Point C}
    (hJ : InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P) :
    InvJ C (tmv C M.n base t p.x) (tmv C M.n base t p.y) (tmv C M.n base t p.z) P := by
  have eqv (x : Nat) (hx : x∈jacCoords p) : tmv C M.n base t x=tmv C M.n base s x := by
    unfold tmv; rw [hk.slot hL hAcc hs hW (hp x hx) (hDisj x hx)]
  rw [eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords])]
  exact hJ

end VG.Proof.Weierstrass.X86
