import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableState

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem copyPointFields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {q o : Pt} (hN : (jacCoords o).Nodup)
    (hqa : ∀ x∈jacCoords q, ∀ y∈jacCoords o, x≠y)
    (hO : ∀ x∈jacCoords o, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x∈jacCoords q, x∈V) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ∃ E', ProgKeep M base (jacCoords o) s t ∧
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
  refine WP.mono (copyField_ok hL hAl hI hox hqx) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl ia hoy (List.mem_cons_of_mem _ hqy)) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAl ib hoz
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

theorem ProgKeep.invJ {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {s t : State} {W : List Nat} (hL : Lay M size Sl) (hs : Scr s base size)
    (hk : ProgKeep M base W s t) (hW : ∀ x∈W, Sl x) {p : Pt}
    (hp : ∀ x∈jacCoords p, Sl x) (hDisj : ∀ x∈jacCoords p, x∉W) {P : Point C}
    (hJ : InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P) :
    InvJ C (tmv C M.n base t p.x) (tmv C M.n base t p.y) (tmv C M.n base t p.z) P := by
  have eqv (x : Nat) (hx : x∈jacCoords p) : tmv C M.n base t x=tmv C M.n base s x := by
    unfold tmv; rw [hk.slot hL hs hW (hp x hx) (hDisj x hx)]
  rw [eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords])]
  exact hJ

end VG.Proof.Weierstrass.AArch64
