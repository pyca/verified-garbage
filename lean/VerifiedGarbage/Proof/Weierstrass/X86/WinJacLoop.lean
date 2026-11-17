module

public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.X86.WinJacEntryState
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
public import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildState
public import VerifiedGarbage.Impl.Weierstrass.X86.CachedJac
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! ### `Weierstrass.X86.WinJacNeg`, which only this module used -/

section

/-! Conditional Y negation without changing the cached powers of Z. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem neg_fields_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) {Q : Point C} {s₀ s : State}
    (h : Frame K C base size wk s₀ s) (he : Entry K C base Q s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa K.tc.negY s fun t => Entry K C base (if Window5.nib v j<16 then negPt Q else Q) t ∧
      ProgKeep K.M base wk [K.neg,K.E.y] s t ∧
      t.gpr .esi=BitVec.ofNat 32 j := by
  obtain hi := h.inv_entry hL hW hro he
  obtain hw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  obtain ez : tmv C K.M.n base s K.zero=0 := by
    unfold tmv at hz ⊢
    rw [h.ro hL hW (by simp [ro])]; exact hz
  obtain hy : K.E.y∈ro K++coords K := by simp [coords]
  obtain hv0 : K.zero∈ro K++coords K := by simp [ro]
  obtain hn := entry_nd hL
  simp only [coords,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  obtain hs : ∀ x∈(FOp.sub K.neg K.zero K.E.y).out::(FOp.sub K.neg K.zero K.E.y).ins,x∈slots K := by
    intro x hx
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [slots,ro,work]
  unfold TCombCfg.negY
  apply WP.seq
  refine WP.mono (fop_ok hL.lay hW hm hi hs (by
    intro x hx
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact hv0
    · exact hy)) fun a ⟨ka,ia⟩ => ?_
  obtain kaw : ProgKeep K.M base wk [K.neg,K.E.y] s a := ka.mono (by simp [FOp.out])
  obtain aa := h.field hL hW kaw hw
  obtain bs : ∀ i<260,a.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [aa.bits hL hi]; exact hb i hi
  obtain hbs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc aa.scr (k:=v) (N:=260)
    (by change 1≤5; decide) (by change 5<2^31; decide) (by change 5*j+5≤260; omega_using [hj]) hbs
    ((ka.gpr _ (by decide)).trans hc) bs) fun b ⟨cb,kb⟩ => ?_
  obtain ib := ia.of_keeps kb (by decide)
  obtain kbk : ProgKeep K.M base wk [K.neg,K.E.y] a b := (keep_of_ckeeps (kb.mono (by decide))).mono (by simp)
  refine WP.mono (choose_field_ok hL.lay hW ib (o:=K.E.y) (by simp [slots,work])
    (a:=K.E.y) (List.mem_cons_of_mem _ hy) (b:=K.neg) (by simp [FOp.out])
    (decide (Window5.nib v j<16)) (by simpa only [JacWinCfg.tc,Window5.combWin_five] using cb))
    fun t ⟨kt,it⟩ => ?_
  obtain kk := kaw.trans (kbk.trans (kt.mono (by simp)))
  refine ⟨?_,kk,(kk.gpr _ (by decide)).trans hc⟩
  apply Entry.of_inv it
  · intro x hx
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  all_goals
    simp only [FOp.run,Function.update_apply,ez]
    simp (disch := nd_find hn) only [ite_eq_right,ite_true]
  · have esub : 0-tmv C K.M.n base s K.E.y = -tmv C K.M.n base s K.E.y := by grind
    by_cases hsign : Window5.nib v j<16
    · simpa only [hsign,decide_true,ite_true,esub] using he.jac.negY
    · simpa only [hsign,decide_false,Bool.false_eq_true,ite_false] using he.jac
  · exact he.z2
  · exact he.z3

end VG.Proof.Weierstrass.X86.JWin

end

end

/-! ### `Weierstrass.X86.WinJacChoosePoint`, which only this module used -/

section

/-! ### `Weierstrass.X86.CachedJacField`, which only this module used -/

section

/-! The cached header and tail compute the same Jacobian addition formula. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.CachedJac
open VG VG.Impl.Weierstrass VG.Impl.Weierstrass.X86

def headN : List FOp :=
  [.mul 0 13 13,.mul 2 11 17,.mul 3 14 0,.mul 4 12 18,
   .mul 5 15 13,.mul 5 5 0,.sub 3 3 2,.sub 5 5 4]

def rename (n : Nat) (S : RcbSlots) (p q o : Pt) (dst i : Nat) : Nat :=
  if i=17 then dst else if i=18 then dst+8*n else rcbσ S p q o i

theorem rename_inj {n : Nat} {S : RcbSlots} {p q o : Pt} {dst : Nat}
    (hA : RcbApart S p q o) (h2 : dst∉rcbW S o) (h3 : dst+8*n∉rcbW S o)
    {w : Nat} (hw : w<9) (y : Nat) (he : rename n S p q o dst y=rename n S p q o dst w) : y=w := by
  obtain hn17 : w≠17 := by omega_using [hw]
  obtain hn18 : w≠18 := by omega_using [hw]
  simp only [rename,hn17,hn18,ite_false] at he
  split at he
  · exact False.elim (h2 (he.symm ▸ rcbσ_out S p q o hw))
  · split at he
    · exact False.elim (h3 (he.symm ▸ rcbσ_out S p q o hw))
    · exact hA.inj hw y he

theorem head_eq (n : Nat) (S : RcbSlots) (p q o : Pt) (dst : Nat) :
    Impl.Weierstrass.X86.CachedJac.head n S p q dst=headN.map (FOp.rename (rename n S p q o dst)) := rfl

theorem tail_eq (n : Nat) (S : RcbSlots) (p q o : Pt) (dst : Nat) :
    jacTail S p q o=jacTailN.map (FOp.rename (rename n S p q o dst)) := rfl

theorem rename_out (n : Nat) (S : RcbSlots) (p q o : Pt) (dst i : Nat) (hi : i<9) :
    rename n S p q o dst i∈rcbW S o := by
  simp only [rename,show i≠17 from by omega_using [hi],show i≠18 from by omega_using [hi],ite_false]
  exact rcbσ_out S p q o hi

theorem rename_mem (n : Nat) (S : RcbSlots) (p q o : Pt) (dst i : Nat) :
    rename n S p q o dst i∈(rcbW S o++rcbR S p q)++[dst,dst+8*n] := by
  unfold rename
  split
  · simp
  · split
    · simp
    · exact List.mem_append_left _ (rcbσ_mem S p q o i)

theorem slots {n : Nat} {N : List FOp} {S : RcbSlots} {p q o : Pt} {dst : Nat} :
    ∀ op∈N.map (FOp.rename (rename n S p q o dst)),∀ x∈op.out::op.ins,
      x∈(rcbW S o++rcbR S p q)++[dst,dst+8*n] := by
  intro op hop
  obtain ⟨op',_,rfl⟩ := List.mem_map.mp hop
  cases op' <;> simp only [FOp.rename,FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,
    or_false] <;> rintro x (rfl|rfl|rfl) <;> exact rename_mem ..

theorem out {n : Nat} {N : List FOp} (hN : ∀ op∈N,op.out<9) {S : RcbSlots} {p q o : Pt} {dst : Nat}
    {op : FOp} (hop : op∈N.map (FOp.rename (rename n S p q o dst))) : op.out∈rcbW S o := by
  obtain ⟨op',hop',rfl⟩ := List.mem_map.mp hop
  rw [FOp.out_rename]
  exact rename_out n S p q o dst _ (hN op' hop')

theorem full_values {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F)
    (h2 : E 17=E 16*E 16) (h3 : E 18=E 17*E 16) :
    (runOps (headN++jacTailN) E 6,runOps (headN++jacTailN) E 7,runOps (headN++jacTailN) E 8)=
      jacAddF (E 11) (E 12) (E 13) (E 14) (E 15) (E 16) := by
  simp only [headN,jacTailN,jacTail,List.cons_append,List.nil_append,
    runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply,↓reduceIte,Nat.reduceEqDiff]
  simp only [h3,h2,jacAddF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem full_run {F : Type _} [Lean.Grind.CommRing F] {n : Nat} {S : RcbSlots} {p q o : Pt} {dst : Nat}
    (hA : RcbApart S p q o) (h2a : dst∉rcbW S o) (h3a : dst+8*n∉rcbW S o)
    (E : Nat → F) (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*n)=E dst*E q.z) :
    let ops := Impl.Weierstrass.X86.CachedJac.head n S p q dst++jacTail S p q o
    (runOps ops E o.x,runOps ops E o.y,runOps ops E o.z)=
      jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  dsimp only
  rw [head_eq n S p q o dst,tail_eq n S p q o dst,←List.map_append]
  obtain he := runOps_rename (rename n S p q o dst) (headN++jacTailN) E
    (fun op hop => rename_inj hA h2a h3a
      ((show ∀ op∈headN++jacTailN,op.out<9 by decide) op hop))
  exact (congrArg₂ Prod.mk (congrFun he 6)
    (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans
      (full_values (fun i => E (rename n S p q o dst i)) h2 h3)

end VG.Proof.Weierstrass.X86.CachedJac

end

end


/-! ## `WinJacAdd` -/

@[expose] public section

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
  obtain e3 : K.z2+8*4=K.z3 := by simp only [JacWinCfg.z2,JacWinCfg.z3,Nat.add_assoc]
  obtain eqops : K.addOps=(CachedJac.headN++jacTailN).map
      (FOp.rename (CachedJac.rename 4 K.S K.R K.E K.D K.z2)) := by
    rw [JacWinCfg.addOps,JacWinCfg.addHead,CachedJac.head_eq 4 K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq 4 K.S K.R K.E K.D K.z2,List.map_append]
  obtain hr : readsOk K.addOps V=true := by
    rw [eqops]
    refine readsOk_mono (readsOk_rename (CachedJac.rename 4 K.S K.R K.E K.D K.z2)
      (show readsOk (CachedJac.headN++jacTailN) [9,10,11,12,13,14,15,16,17,18]=true by decide)) ?_
    simpa [CachedJac.rename,rcbσ,rcbW,rcbR,e3] using hV
  obtain hs : ∀ op∈K.addOps,∀ x∈op.out::op.ins,Sl x := by
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
  obtain ar := hL.readonly K.S.a (by simp [ro])
  obtain br := hL.readonly K.S.b3 (by simp [ro])
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

theorem choose_point_ok {F : Impl.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr}
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
  obtain hin : ∀ x∈[o.x,o.y,o.z,a.x,a.y,a.z],x+8*M.n≤size := by
    intro x hx; exact hL.le x (hI.sl x (hv x hx))
  obtain hoo := And.intro (hL.apart o.x o.y (os _ (by simp [jacCoords])) (os _ (by simp [jacCoords])) ho'.1.1)
    (And.intro (hL.apart o.x o.z (os _ (by simp [jacCoords])) (os _ (by simp [jacCoords])) ho'.1.2)
      (hL.apart o.y o.z (os _ (by simp [jacCoords])) (os _ (by simp [jacCoords])) ho'.2.1))
  refine WP.mono (selPtKeep_ok hI.scr c hc hin hoo
    (fun x hx y hy => hL.apart x y (os x hx) (as y hy) (hd x hx y hy))) fun t ⟨ex,ey,ez,kt,ut⟩ => ?_
  obtain hk : ProgKeep M base wk (jacCoords o) s t := by
    refine ⟨fun r hr => kt.gpr r (fun he => hr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl <;> simp [clob])),kt.rd,kt.wr,?_⟩
    intro x hx
    apply ut x
    · exact hx (o.x,8*M.n) (by simp [progW,jacCoords])
    · exact hx (o.y,8*M.n) (by simp [progW,jacCoords])
    · exact hx (o.z,8*M.n) (by simp [progW,jacCoords])
  obtain hl : ∀ x∈jacCoords o,wordsVal t.mem base x M.n<m := by
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
  obtain he := toM_eq_zero_iff hm (hi.lt z hz)
  rw [hi.val z hz] at he
  exact ct.trans (congrArg bmask (decide_eq_decide.mpr (not_congr he.symm)))

end VG.Proof.Weierstrass.X86.JWin

end

end

end

/-! ### `Weierstrass.X86.WinJacAddMath`, which only this module used -/

section

/-! The two branchless selections make each nonexceptional window addition total. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG Spec.Weierstrass

def addResult {C : Curve} (a : Nat) (R E : Fe C × Fe C × Fe C) : Fe C × Fe C × Fe C :=
  if a=0 then R else if R.2.2=0 then E else jacAddF R.1 R.2.1 R.2.2 E.1 E.2.1 E.2.2

theorem winPt_ne {C : Curve} (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P=true)
    (hP0 : P≠.infinity) (hn : 17≤C.n) {v j : Nat} (ha : magH 16 (Window5.nib v j)≠0) :
    Window5.winPt C P v j≠.infinity := by
  obtain hb : magH 16 (Window5.nib v j)≤16 := magH_le (Nat.mod_lt _ (by decide))
  obtain hm := Window5.mul_ne_infinity hO hP hP0 (by omega_using [ha] : 1≤magH 16 (Window5.nib v j)) (by omega_using [hn, hb])
  rw [Window5.winPt_mag]
  split
  · cases hp : mul (magH 16 (Window5.nib v j)) P with
    | infinity => exact False.elim (hm hp)
    | affine x y => intro he; cases he
  · exact hm

theorem add_result_ok {C : Curve} (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (hn17 : C.n%32=17) (hn64 : 64≤C.n) {k J j : Nat} (hk : k<C.n) (hj : j<J)
    {R E : Fe C × Fe C × Fe C}
    (hR : InvJ C R.1 R.2.1 R.2.2 (mul (32*Window5.winE (k+16*Window5.geom J) J (j+1)) P))
    (hE : InvJ C E.1 E.2.1 E.2.2 (Window5.winPt C P (k+16*Window5.geom J) j)) :
    let t := addResult (magH 16 (Window5.nib (k+16*Window5.geom J) j)) R E
    InvJ C t.1 t.2.1 t.2.2 (mul (Window5.winE (k+16*Window5.geom J) J j) P) := by
  obtain he := Window5.win_add hC hP (k:=k+16*Window5.geom J) (Nat.le_add_left _ _) hj
  dsimp only [addResult]
  split
  next hz =>
    rw [Window5.winPt_zero hz] at he
    obtain he' : mul (32*Window5.winE (k+16*Window5.geom J) J (j+1)) P =
        mul (Window5.winE (k+16*Window5.geom J) J j) P := by
      cases hp : mul (32*Window5.winE (k+16*Window5.geom J) J (j+1)) P <;>
        simpa only [hp,Spec.Weierstrass.add] using he
    rw [←he']; exact hR
  next hz =>
    split
    next rz =>
      rw [(hR.z_zero_iff hC).mp rz] at he
      rw [←he]; exact hE
    next rz =>
      obtain ez : E.2.2≠0 := fun he => winPt_ne hO hP hP0 (by omega_using [hn17]) hz ((hE.z_zero_iff hC).mp he)
      obtain he1 : 1≤Window5.winE (k+16*Window5.geom J) J (j+1) := by
        by_contra he1
        obtain he0 : Window5.winE (k+16*Window5.geom J) J (j+1)=0 := by omega_using [he1]
        apply rz
        apply (hR.z_zero_iff hC).mpr
        rw [he0,Nat.mul_zero,Window5.mul_zero_pt]
      obtain noexc := Window5.loop_noexc hC hO hP hP0 (Nat.le_of_eq hn17.symm) hn64 hk hj he1
      obtain hp := hC.onCurve_mul hP (32*Window5.winE (k+16*Window5.geom J) J (j+1))
      obtain hq := Window5.onCurve_winPt hC hP (k+16*Window5.geom J) j
      obtain hh : E.1*(R.2.2*R.2.2)-R.1*(E.2.2*E.2.2)≠0 := by
        intro hh
        by_cases hy : E.2.1*R.2.2*(R.2.2*R.2.2)-R.2.1*E.2.2*(E.2.2*E.2.2)=0
        · exact noexc.1 (hR.same hC hE rz ez hh hy)
        · exact noexc.2 (hR.opposite hC hp hq hE rz ez hh hy)
      rw [←he]
      exact hR.add_ne hC ha hp hq hE rz ez hh

end VG.Proof.Weierstrass.X86.JWin

end

end

/-! ### `Weierstrass.X86.WinJacFinish`, which only this module used -/

section

/-! One final conversion from Jacobian to homogeneous coordinates. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem finish_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    (hL : Layout K size wk) (hAcc : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p)
    (hOneM : toM C.p (2^(64*K.M.n)) K.one=1)
    {P : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : wordsVal s₀.mem base K.zero K.M.n=0) :
    WP isa K.finish s fun t =>
      ProgKeep K.M base wk (work K) s t ∧ ModOkW K.M size C.p t.mem base ∧
      (∀ x∈jacCoords K.R,wordsVal t.mem base x K.M.n<C.p) ∧
      (k<C.n → Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul e P)) := by
  obtain hi := h.inv hL hAcc hro
  obtain vr0 : ∀ x∈jacCoords K.R,x∈ro K++[K.R.x,K.R.y,K.R.z] := fun _ hx => List.mem_append_right _ hx
  obtain zero : wordsVal s.mem base K.zero K.M.n=0 := by
    rw [h.frame.ro hL hAcc (by simp [ro])]; exact hz
  obtain wr : ∀ x∈jacCoords K.R,x∈work K := by
    intro x hx; simp only [jacCoords,work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  obtain sl : ∀ x∈jacCoords K.R,x∈slots K := fun x hx => List.mem_append_right _ (wr x hx)
  obtain lt := fun x hx => hi.lt x (vr0 x hx)
  have hn := hL.nd
  simp only [work,temps,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  obtain hxy : K.R.x≠K.R.y := by grind
  obtain hzy : K.R.z≠K.R.y := by grind
  obtain hpn := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hi.mod.val] at hpn
  obtain hzero : K.zero∈slots K := List.mem_append_left _ (by simp [ro])
  obtain hy0 := hL.lay.apart K.R.y K.zero (sl _ (by simp [jacCoords])) hzero
    (fun he => hL.readonly K.zero (by simp [ro]) (he ▸ wr _ (by simp [jacCoords])))
  unfold JacWinCfg.finish
  apply WP.seq
  refine WP.mono (outFix_ok K.tc hi.scr (by change 1≤K.M.n; rw [hL.n]; decide)
    (Nat.lt_trans hOne hpn) (hL.lay.le _ (sl K.R.y (by simp [jacCoords])))
    (hL.lay.le _ (sl K.R.z (by simp [jacCoords]))) (hL.lay.le _ hzero) hy0 zero)
    fun a ⟨ya,ka,oa⟩ => ?_
  simp only [JacWinCfg.tc] at ya oa
  obtain pa : ProgKeep K.M base wk [K.R.y] s a :=
    ⟨fun r hr => ka.gpr r (fun he => hr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> simp [clob])),ka.rd,ka.wr,
      Outs.of_outside oa (by simp [progW])⟩
  obtain la : wordsVal a.mem base K.R.y K.M.n<C.p := by
    rw [ya]
    by_cases hz : wordsVal s.mem base K.R.z K.M.n=0
    · simpa only [hz,↓reduceIte] using hOne
    · simpa only [hz,↓reduceIte] using lt K.R.y (by simp [jacCoords])
  obtain ey : toM C.p (2^(64*K.M.n)) (wordsVal a.mem base K.R.y K.M.n)=
      if tmv C K.M.n base s K.R.z=0 then 1 else tmv C K.M.n base s K.R.y := by
    rw [ya]
    by_cases hz : wordsVal s.mem base K.R.z K.M.n=0
    · have hz' : tmv C K.M.n base s K.R.z=0 := by unfold tmv; rw [hz,toM_zero]
      simp only [hz,hz',↓reduceIte]; exact hOneM
    · have hz' : tmv C K.M.n base s K.R.z≠0 := fun he =>
        hz ((toM_eq_zero_iff hm (lt _ (by simp [jacCoords]))).mp he)
      simp only [hz,hz',↓reduceIte]
  let E := Function.update (tmv C K.M.n base s) K.R.y
    (if tmv C K.M.n base s K.R.z=0 then 1 else tmv C K.M.n base s K.R.y)
  obtain ia : Inv K.M base size C.p (·∈slots K) (jacCoords K.R) E a :=
    (hi.update hL.lay hAcc (sl _ (by simp [jacCoords])) pa la ey).sub
      (fun x hx => List.mem_cons_of_mem _ (vr0 x hx))
  obtain opsSl : ∀ op∈K.tc.outOps,∀ x∈op.out::op.ins,x∈slots K := by
    intro op hop x hx
    apply List.mem_append_right
    simp only [TCombCfg.outOps,JacWinCfg.tc,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
      rcases hx with rfl|rfl|rfl <;> simp [work,temps]
  refine WP.mono (fprog_ok hL.lay hAcc hm K.tc.outOps ia opsSl
    (by simp [readsOk,TCombCfg.outOps,JacWinCfg.tc,jacCoords,FOp.ins,FOp.out])) fun t ⟨pt,it⟩ => ?_
  obtain vr : ∀ x∈jacCoords K.R,x∈validAfter K.tc.outOps (jacCoords K.R) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  refine ⟨(pa.mono (by intro x hx; rw [List.mem_singleton.mp hx]; exact wr _ (by simp [jacCoords]))).trans
    (pt.mono (by
      intro x hx
      simp only [TCombCfg.outOps,JacWinCfg.tc,FOp.out,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [work,temps])),it.mod,fun x hx => it.lt x (vr x hx),?_⟩
  intro hk
  obtain ev : ∀ x∈jacCoords K.R,tmv C K.M.n base t x=runOps K.tc.outOps E x :=
    fun x hx => it.val x (vr x hx)
  rw [ev _ (by simp [jacCoords]),ev _ (by simp [jacCoords]),ev _ (by simp [jacCoords])]
  obtain hxt : K.R.x≠K.S.t0 := by grind
  obtain hzt : K.R.z≠K.S.t0 := by grind
  obtain hxz : K.R.x≠K.R.z := by grind
  obtain hyt : K.R.y≠K.S.t0 := by grind
  simp only [TCombCfg.outOps,JacWinCfg.tc,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply,
    hxt,hzt,hxz,hyt,hzy.symm,hxz.symm,hxt.symm,hxy.symm,ite_true,ite_false]
  simp only [E,Function.update_of_ne hxy,Function.update_of_ne hzy,Function.update_self]
  exact InvJ.out hC (h.point hk)

end VG.Proof.Weierstrass.X86.JWin

end

end

/-! ### `Weierstrass.X86.WinJacRead`, which only this module used -/

section

/-! Read a signed-window magnitude and scan both packed tables. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem read_fields_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {P : Point C} {s₀ s : State} (h : Frame K C base size wk s₀ s)
    (ht : Table K C base P 16 s)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa (.block (K.tc.digit++K.select)) s fun t =>
      Entry K C base (mul (magH 16 (Window5.nib v j)) P) t ∧
      ProgKeep K.M base wk (coords K) s t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  obtain hs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega_arith
  obtain bits : ∀ i<260,s.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [h.bits hL hi]; exact hb i hi
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc h.scr (k:=v) (N:=260) (by change 1≤5; decide) (by change 5<9; decide)
    (by change 5*j+5≤260; omega_using [hj]) hs hc bits) fun a ⟨_,ma,ka⟩ => ?_
  obtain kp : ProgKeep K.M base wk [] s a := keep_of_ckeeps (ka.mono (by decide))
  obtain ac := h.field hL hW kp (by simp)
  obtain ea : a.gpr .ebx=BitVec.ofNat 32 (magH 16 (Window5.nib v j)) := by
    simpa only [JacWinCfg.tc,TCombCfg.H,Window5.combWin_five] using ma
  obtain mag : magH 16 (Window5.nib v j)≤16 := magH_le (by
    have := Nat.mod_lt (v/32^j) (show 0<32 by decide)
    change Window5.nib v j<2*16
    exact this)
  refine WP.mono (select_entry_ok hL ac.scr mag ea (ht.field_keep hL h.scr kp (by simp) (by decide))) fun t ⟨pt,kt⟩ => ?_
  refine ⟨pt,(kp.mono (by simp)).trans kt,?_⟩
  exact (kt.gpr _ (by decide)).trans ((ka.1 _ (by decide)).trans hc)

end VG.Proof.Weierstrass.X86.JWin

end

end


/-! ## `WinJacFirst` -/

@[expose] public section

section

/-! Seed the accumulator from the top signed digit, avoiding five doublings. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem first_value {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P=true)
    {v J : Nat} (hJ : 1≤J) (hlo : 16*Window5.geom J≤v) (hhi : v<32^J) :
    Window5.winPt C P v (J-1)=mul (Window5.winE v J (J-1)) P := by
  obtain he := Window5.win_add hC hP hlo (show J-1<J by omega_arith)
  rw [show J-1+1=J by omega_arith,Window5.winE_top hhi,Nat.mul_zero,Window5.mul_zero_pt] at he
  exact he

theorem first_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k v : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) {P : Point C} (hP : onCurve C P=true)
    {s₀ s : State} (hf : Frame K C base size wk s₀ s) (ht : Table K C base P 16 s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if v.testBit i then 1 else 0)
    (hlo : 16*Window5.geom K.J≤v) (hhi : v<32^K.J) :
    WP isa K.first s fun t => Accum K C base size wk P k s₀ (Window5.winE v K.J (K.J-1)) t ∧
      t.gpr .esi=BitVec.ofNat 32 (K.J-1) := by
  unfold JacWinCfg.first
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (mov_counter_ok s (K.J-1)) fun a ⟨ca,ka⟩ => ?_
  obtain fa := hf.keeps ka
  obtain ta : Table K C base P 16 a := fun m h1 hm => (ht m h1 hm).congr fun _ _ => by rw [ka.2.1]
  obtain hj : K.J-1<52 := by have := hL.J; omega_arith
  refine WP.mono (read_fields_ok hL hW fa ta hj ca hb) fun b ⟨pb,kb,cb⟩ => ?_
  obtain fb := fa.field hL hW kb (coords_work K)
  obtain tb := ta.field_keep hL fa.scr kb (coords_work K) (by decide)
  apply WP.seq
  refine WP.mono (neg_fields_ok hL hW hm fb pb hro hz hj cb hb) fun c ⟨pc,kc,cc⟩ => ?_
  obtain nw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  obtain fc := fb.field hL hW kc nw
  obtain tc := tb.field_keep hL fb.scr kc nw (by decide)
  obtain ic := fc.inv_entry hL hW hro pc
  obtain hn : (jacCoords K.R).Nodup := by
    apply List.Nodup.sublist (l₂:=rcbW K.S K.R) _ (rcb_R_nd hL)
    simp only [jacCoords,rcbW]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  obtain rwk : ∀ x∈jacCoords K.R,x∈work K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [work]
  obtain ev : ∀ x∈jacCoords K.E,x∈ro K++coords K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [coords]
  obtain sep : ∀ x∈jacCoords K.E,∀ y∈jacCoords K.R,x≠y := by
    intro x hx y hy he
    apply entry_apart_R hL y hy
    rw [←he]
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [coords]
  rw [←hL.n]
  refine WP.mono (copyPointFields_ok hL.lay hW hn sep
    (fun x hx => List.mem_append_right _ (rwk x hx)) ic ev) fun t ⟨et,kt,it,vt⟩ => ?_
  refine ⟨⟨fc.field hL hW kt rwk,tc.field_keep hL fc.scr kt rwk (by decide),
    fun x hx => it.lt x (List.mem_append_left _ hx),?_⟩,(kt.gpr _ (by decide)).trans cc⟩
  intro _
  apply it.point_tmv (fun _ hx => List.mem_append_left _ hx)
  simp only [Prod.mk.injEq] at vt
  rw [vt.1,vt.2.1,vt.2.2]
  have jp := pc.jac
  obtain he : (if Window5.nib v (K.J-1)<16 then negPt (mul (magH 16 (Window5.nib v (K.J-1))) P)
      else mul (magH 16 (Window5.nib v (K.J-1))) P)=Window5.winPt C P v (K.J-1) := by
    simpa using (Window5.winPt_mag P v (K.J-1)).symm
  rw [he,first_value hC hP (by have := hL.J; omega_arith) hlo hhi] at jp
  exact jp

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacRepair` -/

section

/-! Branchless corrections for a zero accumulator or zero signed digit. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem repair_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk v j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hv : ∀ x∈jacCoords K.R++jacCoords K.D++jacCoords K.E,x∈V)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s.mem (off base (K.bits+i))=if v.testBit i then 1 else 0) :
    WP isa (.block (nzMask 4 K.R.z++selPt 4 K.D K.E K.D++K.tc.digit++eqMask 0++selPt 4 K.R K.D K.R))
      s fun t => ∃ E', ProgKeep K.M base wk (jacCoords K.D++jacCoords K.R) s t ∧
      Inv K.M base size C.p (·∈slots K) (jacCoords K.R++(jacCoords K.D++V)) E' t ∧
      (E' K.R.x,E' K.R.y,E' K.R.z)=
        (if magH 16 (Window5.nib v j)=0 then (E K.R.x,E K.R.y,E K.R.z)
         else if E K.R.z=0 then (E K.E.x,E K.E.y,E K.E.z) else (E K.D.x,E K.D.y,E K.D.z)) := by
  obtain vr : ∀ x∈jacCoords K.R,x∈V := fun x hx => hv x (List.mem_append_left _ (List.mem_append_left _ hx))
  obtain vd : ∀ x∈jacCoords K.D,x∈V := fun x hx => hv x (List.mem_append_left _ (List.mem_append_right _ hx))
  obtain ve : ∀ x∈jacCoords K.E,x∈V := fun x hx => hv x (List.mem_append_right _ hx)
  obtain dw : ∀ x∈jacCoords K.D,x∈work K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [work]
  obtain rwk : ∀ x∈jacCoords K.R,x∈work K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [work]
  rw [List.append_assoc,List.append_assoc,List.append_assoc,WP.block_append_iff]
  obtain hmz := nz_field_ok (wk:=wk) hL.lay hm hi (vr K.R.z (by simp [jacCoords]))
  rw [hL.n] at hmz
  refine WP.mono hmz fun a ⟨ca,ia,ka⟩ => ?_
  rw [WP.block_append_iff,←hL.n]
  refine WP.mono (choose_point_ok hL.lay hW ia (point_nd hL (Or.inr (Or.inl rfl))) (points_apart hL).1
    (fun x hx => (List.mem_append.mp hx).elim (vd x) (ve x))
    (decide (E K.R.z≠0)) ca) fun b ⟨eb,kb,ib,ebd⟩ => ?_
  obtain kab : ProgKeep K.M base wk (jacCoords K.D) s b := (ka.mono (by simp)).trans kb
  obtain fb := (Frame.refl hi.scr hi.mod).field hL hW kab dw
  obtain bs : ∀ i<260,b.mem (off base (K.bits+i))=if v.testBit i then 1 else 0 := by
    intro i hi; rw [fb.bits hL hi]; exact hb i hi
  obtain hbs : K.bits+260≤size := by have := hL.bits; have := hL.table; omega_arith
  obtain cb : b.gpr .esi=BitVec.ofNat 32 j := (kab.gpr _ (by decide)).trans hc
  have er (x : Nat) (hx : x∈jacCoords K.R) : eb x=E x :=
    value_after hL.lay hW hi ib kab (fun x hx => List.mem_append_right _ (dw x hx))
      (vr x hx) (List.mem_append_right _ (vr x hx)) (fun hd => (points_apart hL).2 x hx x hd rfl)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc ib.scr (k:=v) (N:=260) (by change 1≤5; decide) (by change 5<9; decide)
    (by change 5*j+5≤260; omega_arith) hbs cb bs) fun c ⟨_,mc,kc⟩ => ?_
  obtain cm : c.gpr .ebx=BitVec.ofNat 32 (magH 16 (Window5.nib v j)) := by
    simpa only [JacWinCfg.tc,TCombCfg.H,Window5.combWin_five] using mc
  obtain mag : magH 16 (Window5.nib v j)≤16 := magH_le (Nat.mod_lt _ (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok c (by decide) (by omega_arith) cm) fun d ⟨cd,kd,_⟩ => ?_
  obtain kcd : CKeeps clob b d := (kc.mono (by decide)).trans (kd.mono (by decide))
  obtain id := ib.of_keeps kcd (by decide)
  refine WP.mono (choose_point_ok hL.lay hW id (point_nd hL (Or.inl rfl)) (points_apart hL).2
    (fun x hx => (List.mem_append.mp hx).elim (fun hx => List.mem_append_right _ (vr x hx))
      (fun hx => List.mem_append_left _ hx)) (decide (magH 16 (Window5.nib v j)=0)) cd)
    fun t ⟨et,kt,it,etr⟩ => ?_
  obtain kk : ProgKeep K.M base wk (jacCoords K.D++jacCoords K.R) s t :=
    (kab.mono (fun _ hx => List.mem_append_left _ hx)).trans
      (((keep_of_ckeeps kcd).mono (by simp)).trans (kt.mono (fun _ hx => List.mem_append_right _ hx)))
  refine ⟨et,kk,it,?_⟩
  rw [etr,er _ (by simp [jacCoords]),er _ (by simp [jacCoords]),er _ (by simp [jacCoords]),ebd]
  by_cases hz : magH 16 (Window5.nib v j)=0
  · simp only [hz,decide_true,ite_true]
  · simp only [hz,decide_false,Bool.false_eq_true,ite_false]
    by_cases he : E K.R.z=0 <;> simp [he]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacAddStep` -/

section

/-! Cached addition and both branchless corrections for one signed digit. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem add_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (32*Window5.winE (k+16*Window5.geom K.J) K.J (j+1)) s)
    (he : Entry K C base (Window5.winPt C P (k+16*Window5.geom K.J) j) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) (hj : j<K.J)
    (hc : s.gpr .esi=BitVec.ofNat 32 j)
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa (.seq (fprog K.F K.addOps) (.block
      (nzMask 4 K.R.z++selPt 4 K.D K.E K.D++K.tc.digit++eqMask 0++selPt 4 K.R K.D K.R))) s fun t =>
      Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧
      t.gpr .esi=BitVec.ofNat 32 j := by
  obtain hi := h.inv_entry hL hW hro he
  obtain hA := add_apart hL
  obtain sl : ∀ x∈(rcbW K.S K.D++rcbR K.S K.R K.E)++[K.z2,K.z3],x∈slots K := by
    intro x hx
    simp only [rcbW,rcbR,slots,ro,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  obtain hv : ∀ x∈rcbR K.S K.R K.E++[K.z2,K.z3],x∈(ro K++[K.R.x,K.R.y,K.R.z])++coords K := by
    intro x hx
    simp only [rcbR,ro,coords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply WP.seq
  refine WP.mono (cadd_ok hL.lay hW hm hA.1 hA.2.1 hA.2.2 sl hi hv he.z2 he.z3)
    fun a ⟨ka,ia,da⟩ => ?_
  obtain fa := h.frame.field hL hW ka (rcb_D_work K)
  obtain ba : ∀ i<260,a.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0 := by
    intro i hi; rw [fa.bits hL hi]; exact hb i hi
  have read (x : Nat) (hx : x∈rcbR K.S K.R K.E) :
      runOps K.addOps (tmv C K.M.n base s) x=tmv C K.M.n base s x :=
    value_after hL.lay hW hi ia ka (fun x hx => List.mem_append_right _ (rcb_D_work K x hx))
      (hv x (List.mem_append_left _ hx))
      (List.mem_append_right _ (hv x (List.mem_append_left _ hx))) (hA.1.apart x hx)
  obtain va : ∀ x∈jacCoords K.R++jacCoords K.D++jacCoords K.E,
      x∈[K.D.x,K.D.y,K.D.z]++((ro K++[K.R.x,K.R.y,K.R.z])++coords K) := by
    intro x hx
    simp only [jacCoords,coords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono (repair_ok hL hW hm ia va (by have := hL.J; omega_arith)
    ((ka.gpr _ (by decide)).trans hc) ba) fun t ⟨et,kt,it,vt⟩ => ?_
  obtain kw : ∀ x∈jacCoords K.D++jacCoords K.R,x∈work K := by
    intro x hx
    simp only [jacCoords,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine ⟨⟨fa.field hL hW kt kw,
    (h.table.field_keep hL h.frame.scr ka (rcb_D_work K) (by decide)).field_keep hL ia.scr kt kw (by decide),
    fun x hx => it.lt x (List.mem_append_left _ hx),?_⟩,
    (kt.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hc)⟩
  intro hk
  apply it.point_tmv (fun _ hx => List.mem_append_left _ hx)
  change (fun q : Fe C × Fe C × Fe C => InvJ C q.1 q.2.1 q.2.2
    (mul (Window5.winE (k+16*Window5.geom K.J) K.J j) P)) (et K.R.x,et K.R.y,et K.R.z)
  rw [vt,read _ (by simp [rcbR]),read _ (by simp [rcbR]),read _ (by simp [rcbR]),
    read _ (by simp [rcbR]),read _ (by simp [rcbR]),read _ (by simp [rcbR]),da]
  exact add_result_ok hC ha hO hP hP0 hn17 hn64 hk hj (h.point hk) he.jac

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacStep` -/

section

/-! One full signed-window iteration. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem dec_counter_ok {s : State} {j : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 (j+1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 j ∧ CKeeps [.esi] s t := by
  obtain he : BitVec.ofNat 32 (j+1)-(1 : BitVec 32)=BitVec.ofNat 32 j := by
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  crun [hc,he]
  refine ⟨fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem test_counter_ok {s : State} {j : Nat} (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
      t.zf=some (decide (j=0)) ∧ CKeeps [.esi] s t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  obtain he : (BitVec.ofNat 32 j==(0 : BitVec 32))=decide (j=0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this
      have hz : (0 : BitVec 32).toNat=0 := rfl
      omega_arith
    · intro h; subst j; rfl
  crun [hc,BitVec.and_self,RegUpd.zf_arithFlags,he]
  exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩

theorem step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J (j+1)) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hj : j<K.J)
    (hc : s.gpr .esi=BitVec.ofNat 32 (j+1))
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa K.step s fun t => Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧
      t.gpr .esi=BitVec.ofNat 32 j ∧ t.zf=some (decide (j=0)) := by
  obtain hj52 : j<52 := by have := hL.J; omega_arith
  unfold JacWinCfg.step
  apply WP.seq
  refine WP.mono (dec_counter_ok hc) fun a ⟨ca,ka⟩ => ?_
  apply WP.seq
  refine WP.mono (doubles_ok hL hW hm hC ha hP (h.keeps ka) hro hj52 ca) fun b ⟨ab,cb⟩ => ?_
  apply WP.seq
  refine WP.mono (read_fields_ok hL hW ab.frame ab.table hj52 cb hb) fun c ⟨pc,kc,cc⟩ => ?_
  obtain ac := ab.preserve hL hW kc (coords_work K) (fun x hx hy => entry_apart_R hL x hx (List.mem_append_left _ hy))
  apply WP.seq
  refine WP.mono (neg_fields_ok hL hW hm ac.frame pc hro hz hj52 cc hb) fun d ⟨pd,kd,cd⟩ => ?_
  obtain nw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  obtain nr : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉[K.neg,K.E.y] := by
    intro x hx hy
    apply entry_apart_R hL x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl|rfl <;> simp [coords]
  obtain ad := ac.preserve hL hW kd nw nr
  obtain pd : Entry K C base (Window5.winPt C P (k+16*Window5.geom K.J) j) d := by
    obtain ep := Window5.winPt_mag P (k+16*Window5.geom K.J) j
    simpa only [ep,decide_eq_true_eq] using pd
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (add_step_ok hL hW hm hC ha hO hP hP0 hn17 hn64 ad pd hro hj cd hb))
    fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun t ⟨acc_t,ct⟩ => ?_
  refine WP.mono (test_counter_ok hj52 ct) fun z ⟨fz,kz,cz⟩ => ⟨acc_t.keeps kz,cz,fz⟩

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacLoop` -/

section

/-! The complete constant-time signed-window multiplier. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem loop_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J (K.J-1)) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hc : s.gpr .esi=BitVec.ofNat 32 (K.J-1))
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa (.loop K.step .ne) s (Accum K C base size wk P k s₀ k) := by
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j<K.J ∧ Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧ t.gpr .esi=BitVec.ofNat 32 j)
    (fun j u ⟨h1,hj,hu,cu⟩ => ?_) (K.J-1) s
    ⟨by have := hL.J; omega_arith,by have := hL.J; omega_arith,h,hc⟩
  obtain cu' : u.gpr .esi=BitVec.ofNat 32 (j-1+1) := by rw [show j-1+1=j by omega_arith]; exact cu
  obtain hu' : Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J (j-1+1)) u := by
    rw [show j-1+1=j by omega_arith]; exact hu
  refine WP.mono (step_ok hL hW hm hC ha hO hP hP0 hn17 hn64 hu' hro hz (by omega_arith) cu' hb)
    fun t ⟨ht,ct,ft⟩ => ?_
  by_cases he : j=1
  · subst j
    refine Or.inl ⟨?_,?_⟩
    · change Option.map Bool.not t.zf=some false
      rw [ft]; rfl
    · simpa only [Nat.sub_self,Window5.winE_zero,Nat.add_sub_cancel] using ht
  · refine Or.inr ⟨?_,j-1,by omega_arith,by omega_arith,by omega_arith,ht,ct⟩
    change Option.map Bool.not t.zf=some true
    rw [ft,decide_eq_false (by omega_arith)]
    rfl

theorem window_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    (hOne : K.one<C.p) (hOneM : toM C.p (2^(64*K.M.n)) K.one=1)
    {s : State} (hi : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P)
    (hz : tmv C K.M.n base s K.P.z=1) (h0 : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<260,s.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0)
    (hrec : k+16*Window5.geom K.J<32^K.J) :
    WP isa K.window s fun t => Frame K C base size wk s t ∧
      (∀ x∈jacCoords K.R,wordsVal t.mem base x K.M.n<C.p) ∧
      (k<C.n → Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul k P)) := by
  obtain zero : tmv C K.M.n base s K.zero=0 := by unfold tmv; rw [h0,toM_zero]
  unfold JacWinCfg.window
  apply WP.seq
  refine WP.mono (build_ok hL hW hm hC ha hO (by omega_arith) hP hP0 hi hJ hz) fun a ba => ?_
  apply WP.seq
  refine WP.mono (first_ok (k:=k) hL hW hm hC hP ba.frame ba.table hi.lt zero hb (Nat.le_add_left _ _) hrec)
    fun b ⟨ab,cb⟩ => ?_
  apply WP.seq
  refine WP.mono (loop_ok hL hW hm hC ha hO hP hP0 hn17 hn64 ab hi.lt zero cb hb) fun c ac => ?_
  refine WP.mono (finish_ok hL hW hm hC hOne hOneM ac hi.lt h0) fun t ⟨kt,_,lt,rt⟩ =>
    ⟨ac.frame.field hL hW kt (fun _ hx => hx),lt,rt⟩

end VG.Proof.Weierstrass.X86.JWin

end
