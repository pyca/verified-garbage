import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntryState
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd

/-! ## `WinJacAdd` -/

section

/-! The secret-scalar loop's cached-power Jacobian addition. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem cadd_ok {K : JacWinCfg} {base : Addr} {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hW : WkOk K.F K.M m size wk Sl)
    (hm : UnitMod m (2^(64*K.M.n))) (hA : RcbApart K.S K.R K.E K.D)
    (h2a : K.z2∉rcbW K.S K.D) (h3a : K.z3∉rcbW K.S K.D)
    (hSl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.z2,K.z3],Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s)
    (hV : ∀ x∈rcbR K.S K.R K.E++[K.z2,K.z3],x∈V)
    (h2 : E K.z2=E K.E.z*E K.E.z) (h3 : E K.z3=E K.z2*E K.E.z) :
    WP isa (fprog K.F K.addOps) s fun t =>
      ProgKeep K.M base wk (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl ([K.D.x,K.D.y,K.D.z]++V) (runOps K.addOps E) t ∧
      (runOps K.addOps E K.D.x,runOps K.addOps E K.D.y,runOps K.addOps E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have e3 : K.z2+8*4=K.z3 := by simp only [JacWinCfg.z2,JacWinCfg.z3,Nat.add_assoc]
  have eqops : K.addOps=(CachedJac.headN++jacTailN).map
      (FOp.rename (CachedJac.rename 4 K.S K.R K.E K.D K.z2)) := by
    rw [JacWinCfg.addOps,JacWinCfg.addHead,CachedJac.head_eq 4 K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq 4 K.S K.R K.E K.D K.z2,List.map_append]
  have hr : readsOk K.addOps V=true := by
    rw [eqops]
    refine readsOk_mono (readsOk_rename (CachedJac.rename 4 K.S K.R K.E K.D K.z2)
      (show readsOk (CachedJac.headN++jacTailN) [9,10,11,12,13,14,15,16,17,18]=true by decide)) ?_
    simpa [CachedJac.rename,rcbσ,rcbW,rcbR,e3] using hV
  have hs : ∀ op∈K.addOps,∀ x∈op.out::op.ins,Sl x := by
    rw [eqops]
    intro op hop x hx
    apply hSl x
    simpa only [e3] using CachedJac.slots op hop x hx
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr) fun t ⟨kt,it⟩ => ⟨kt.mono ?_,it.sub ?_,?_⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    rw [eqops] at hop
    exact CachedJac.out (show ∀ op∈CachedJac.headN++jacTailN,op.out<9 by decide) hop
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [JacWinCfg.addOps,jacTail,FOp.out]
    · exact Or.inl hx
  · exact CachedJac.full_run hA h2a (by rw [e3]; exact h3a) E h2 (by rw [e3]; exact h3)

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacAddLayout` -/

section

/-! Separate the accumulator, selected point, and addition output. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem rcb_D_work (K : JacWinCfg) : ∀ x∈rcbW K.S K.D,x∈work K := by
  intro x hx
  simp only [rcbW,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem add_apart {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    RcbApart K.S K.R K.E K.D ∧ K.z2∉rcbW K.S K.D ∧ K.z3∉rcbW K.S K.D := by
  have nd := hL.nd
  have ar := hL.readonly K.S.a (by simp [ro])
  have br := hL.readonly K.S.b3 (by simp [ro])
  simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at nd ar br
  refine ⟨⟨?_,?_⟩,?_,?_⟩ <;>
    simp only [rcbW,rcbR,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil,and_true,forall_eq_or_imp,forall_eq] <;> grind

theorem point_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk)
    {p : Pt} (hp : p=K.R ∨ p=K.D ∨ p=K.E) : (jacCoords p).Nodup := by
  rcases hp with rfl|rfl|rfl
  all_goals
    apply List.Nodup.sublist (l₂:=work K) _ hL.nd
    simp only [jacCoords,work,temps,List.cons_append,List.nil_append]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem points_apart {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (∀ x∈jacCoords K.D,∀ y∈jacCoords K.E,x≠y) ∧
    (∀ x∈jacCoords K.R,∀ y∈jacCoords K.D,x≠y) := by
  have hn := hL.nd
  simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  constructor <;> simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;> grind

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacChoosePoint` -/

section

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

end
