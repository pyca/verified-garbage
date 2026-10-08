import VerifiedGarbage.Proof.Weierstrass.X86.WinJacChoose
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJMask
import VerifiedGarbage.Proof.Weierstrass.X86.JacZero

/-! Branchless point selection, with canonical fields and its memory environment. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem choose_point_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr}
    {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a : Pt} (ho : (jacCoords o).Nodup)
    (hd : ∀ x∈jacCoords o,∀ y∈jacCoords a,x≠y)
    (hv : ∀ x∈jacCoords o++jacCoords a,x∈V) (c : Bool) (hc : s.gpr .ecx=bmask c) :
    WP isa (.block (selPt M.n o a o)) s fun t => ∃ E',
      ProgKeep M base wk (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o++V) E' t ∧
      (E' o.x,E' o.y,E' o.z)=(if c then (E o.x,E o.y,E o.z) else (E a.x,E a.y,E a.z)) := by
  have os (x : Nat) (hx : x∈jacCoords o) : Sl x := hI.sl x (hv x (List.mem_append_left _ hx))
  have as (x : Nat) (hx : x∈jacCoords a) : Sl x := hI.sl x (hv x (List.mem_append_right _ hx))
  have ho' := ho
  simp only [jacCoords,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at ho'
  have hin : ∀ x∈[o.x,o.y,o.z,a.x,a.y,a.z],x+8*M.n≤size := by
    intro x hx; exact hL.le x (hI.sl x (hv x hx))
  have hoo := And.intro (hL.apart o.x o.y (os _ (by simp [jacCoords])) (os _ (by simp [jacCoords])) ho'.1.1)
    (And.intro (hL.apart o.x o.z (os _ (by simp [jacCoords])) (os _ (by simp [jacCoords])) ho'.1.2)
      (hL.apart o.y o.z (os _ (by simp [jacCoords])) (os _ (by simp [jacCoords])) ho'.2.1))
  refine WP.mono (selPtKeep_ok hI.scr c hc hin hoo
    (fun x hx y hy => hL.apart x y (os x hx) (as y hy) (hd x hx y hy))) fun t ⟨ex,ey,ez,kt,ut⟩ => ?_
  have hk : ProgKeep M base wk (jacCoords o) s t := by
    refine ⟨fun r hr => kt.gpr r (fun he => hr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl <;> simp [clob])),kt.rd,kt.wr,?_⟩
    intro x hx
    apply ut x
    · exact hx (o.x,8*M.n) (by simp [progW,jacCoords])
    · exact hx (o.y,8*M.n) (by simp [progW,jacCoords])
    · exact hx (o.z,8*M.n) (by simp [progW,jacCoords])
  have hl : ∀ x∈jacCoords o,wordsVal t.mem base x M.n<m := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · rw [ex]; cases c <;> exact hI.lt _ (hv _ (by simp [jacCoords]))
    · rw [ey]; cases c <;> exact hI.lt _ (hv _ (by simp [jacCoords]))
    · rw [ez]; cases c <;> exact hI.lt _ (hv _ (by simp [jacCoords]))
  refine ⟨_,hk,hI.of_progKeep hL hW hk os hl,?_⟩
  rw [ex,ey,ez]
  cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals
    rw [hI.val _ (hv _ (by simp [jacCoords])),hI.val _ (hv _ (by simp [jacCoords])),
      hI.val _ (hv _ (by simp [jacCoords]))]

theorem nz_field_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hi : Inv M base size m Sl V E s) {z : Nat} (hz : z∈V) :
    WP isa (.block (nzMask M.n z)) s fun t =>
      t.gpr .ecx=bmask (decide (E z≠0)) ∧ Inv M base size m Sl V E t ∧ ProgKeep M base wk [] s t := by
  refine WP.mono (nzMask_ok hi.scr hi.mod.n0 (hL.le z (hi.sl z hz))) fun t ⟨ct,kt⟩ =>
    ⟨?_,hi.of_keeps kt (by decide),keep_of_ckeeps (kt.mono (by decide))⟩
  have he := toM_eq_zero_iff hm (hi.lt z hz)
  rw [hi.val z hz] at he
  exact ct.trans (congrArg bmask (decide_eq_decide.mpr (not_congr he.symm)))

end VG.Proof.Weierstrass.X86.JWin
