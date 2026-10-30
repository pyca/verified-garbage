module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.JointDouble
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacDouble
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAddTiming
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# The joint loop's doubler

What the joint loop needs of the curve's doubling of its accumulator
(`JointDoubler`): it doubles the point, writes only the loop's working slots,
and its timing depends on nothing but the working space's address. Any
number of words can use `Joint.jacDouble` (`jacDouble_doubler`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

/-- `double` doubles the joint loop's accumulator `R`, keeping every slot
but the loop's working ones, in time that depends only on `rdi`. -/
structure JointDoubler (c : Joint.Cfg) (C : Curve) (size : Nat) (double : Prog isa) : Prop where
  ok : ∀ {base : Addr} {u v : Nat} {Q A : Point C} {External : State → Prop} {s : State},
    (∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t) →
    onCurve C A=true → JointCore c C base size Q u v External A s →
    WP isa double.inline s fun t => ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v External (add A A) t
  ct : ∀ {base : Addr} {E : Nat → Fe C},
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E) double.inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)

theorem jacDouble_doubler {c : Joint.Cfg} {C : Curve} {size : Nat}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hd : ScratchCT (fprogB c.K.M (dblJMul c.K.S c.K.R c.K.D)).inline)
    (hcp : ScratchCT (.block (copyPt c.K.M.n c.K.R c.K.D))) :
    JointDoubler c C size (Joint.jacDouble c.K) := by
  have apart : RcbApart c.K.S c.K.R c.K.R c.K.D :=
    ⟨hL.addApart.nodup,fun x hx => hL.addApart.apart x (by
      simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)⟩
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.R,x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.R,x∈jointLive c := by intro x hx; jslots
  have rs : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by intro x hx; jslots
  constructor
  · intro base u v Q A External s hExt hA h
    rw [Joint.jacDouble]
    apply WP.seq
    refine WP.mono_syms (jacDouble_ok hL.lookup.layout.lay hm (jdblOk_dblJMul hC ha) apart sl h.field vr hA h.point)
      fun d ⟨kd,id,jd⟩ sd => ?_
    have wd : ∀ x∈rcbW c.K.S c.K.D,x∈jointWork c := by intro x hx; jslots
    have edExt := hExt s d (kd.mono wd) sd h.external
    refine WP.mono_syms (copyPointFields_ok hL.lookup.layout.lay hL.accumNodup hL.copyApart rs id
      (fun _ hx => List.mem_append_left _ hx)) fun t ⟨et,kt,it,jt⟩ st => ?_
    have wr : ∀ x∈jacCoords c.K.R,x∈jointWork c := by intro x hx; jslots
    have kt' := kt.mono wr
    have kw := (kd.mono wd).trans kt'
    have ie := it.sub (fun x hx => List.mem_append_right _ (List.mem_append_right _ hx))
    have jp : InvJ C (et c.K.R.x) (et c.K.R.y) (et c.K.R.z) (add A A) := by
      simp only [Prod.mk.injEq] at jt
      rw [jt.1,jt.2.1,jt.2.2]
      exact jd
    exact ⟨kw,h.next hL.lookup.layout kw ie jp (hExt d t kt' st edExt)⟩
  · intro base E
    rw [Joint.jacDouble]
    apply RelCT.seq (doubleFieldPlain_relCT hL.lookup.layout.lay hm sl vr jdblShape_dblJMul hd)
    have cp := copyPoint_relCT (base:=base) (E:=runOps (dblJMul c.K.S c.K.R c.K.D) E)
      hL.lookup.layout.lay (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
      (V:=[c.K.D.x,c.K.D.y,c.K.D.z]++jointLive c) (by intro x hx; exact List.mem_append_left _ hx) hcp
    exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx =>
      List.mem_append_right _ (List.mem_append_right _ hx))⟩)

/-- The point functions' doubling body (`PointOps.doubleBody`: `D = 2R` by any
doubling `dbl` of `C`, copied back to `R`) is a doubler. -/
theorem doubleBody_doubler {c : Joint.Cfg} {C : Curve} {size : Nat}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    {dbl : RcbSlots → Pt → Pt → List FOp} (hdo : JDblOk C dbl)
    (hd : ScratchCT (fprogB c.K.M (dbl c.K.S c.K.R c.K.D)).inline)
    (hcp : ScratchCT (.block (copyPt c.K.M.n c.K.R c.K.D))) :
    JointDoubler c C size (PointOps.doubleBody c.K dbl) := by
  have apart : RcbApart c.K.S c.K.R c.K.R c.K.D :=
    ⟨hL.addApart.nodup,fun x hx => hL.addApart.apart x (by
      simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)⟩
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.R,x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.R,x∈jointLive c := by intro x hx; jslots
  have rs : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by intro x hx; jslots
  constructor
  · intro base u v Q A External s hExt hA h
    rw [PointOps.doubleBody]
    apply WP.seq
    refine WP.mono_syms (jacDouble_ok hL.lookup.layout.lay hm hdo apart sl h.field vr hA h.point)
      fun d ⟨kd,id,jd⟩ sd => ?_
    have wd : ∀ x∈rcbW c.K.S c.K.D,x∈jointWork c := by intro x hx; jslots
    have edExt := hExt s d (kd.mono wd) sd h.external
    refine WP.mono_syms (copyPointFields_ok hL.lookup.layout.lay hL.accumNodup hL.copyApart rs id
      (fun _ hx => List.mem_append_left _ hx)) fun t ⟨et,kt,it,jt⟩ st => ?_
    have wr : ∀ x∈jacCoords c.K.R,x∈jointWork c := by intro x hx; jslots
    have kt' := kt.mono wr
    have kw := (kd.mono wd).trans kt'
    have ie := it.sub (fun x hx => List.mem_append_right _ (List.mem_append_right _ hx))
    have jp : InvJ C (et c.K.R.x) (et c.K.R.y) (et c.K.R.z) (add A A) := by
      simp only [Prod.mk.injEq] at jt
      rw [jt.1,jt.2.1,jt.2.2]
      exact jd
    exact ⟨kw,h.next hL.lookup.layout kw ie jp (hExt d t kt' st edExt)⟩
  · intro base E
    rw [PointOps.doubleBody]
    apply RelCT.seq (doubleFieldPlain_relCT hL.lookup.layout.lay hm sl vr hdo.shape hd)
    have cp := copyPoint_relCT (base:=base) (E:=runOps (dbl c.K.S c.K.R c.K.D) E)
      hL.lookup.layout.lay (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
      (V:=[c.K.D.x,c.K.D.y,c.K.D.z]++jointLive c) (by intro x hx; exact List.mem_append_left _ hx) hcp
    exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx =>
      List.mem_append_right _ (List.mem_append_right _ hx))⟩)

/-- A call of a doubler that calls nothing, between `saves` and `restores`
(`PointOps.wrap`), is a doubler. -/
theorem call_doubler {c : Joint.Cfg} {C : Curve} {size : Nat} {d : Prog isa}
    (h : JointDoubler c C size d) (hnc : d.noCalls = true)
    (hclob : ∀ r ∈ Proof.Weierstrass.X86_64.PointOps.keptRegs, r ∈ clob c.K.M.n) (n : String) :
    JointDoubler c C size (.call n (PointOps.wrap d)) := by
  have hi := Code.inline_of_noCalls hnc
  constructor
  · intro base u v Q A External s hExt hA hs
    show WP isa (PointOps.wrap d) s _
    refine Proof.Weierstrass.X86_64.PointOps.wrap_keep_ok hclob
      (fun x y pk k sy hx => hx.of_keeps k (by simp) (hExt x y pk sy hx.external))
      (fun x y pk k sy hx => hx.of_keeps k (by decide) (hExt x y pk sy hx.external)) hs
      fun x hx => ?_
    have := h.ok hExt hA hx
    rwa [hi] at this
  · intro base E
    show RelCT isa _ (PointOps.wrap d) _
    have := h.ct (base := base) (E := E)
    rw [hi] at this
    exact Proof.Weierstrass.X86_64.PointOps.wrap_relCT this

end VG.Proof.Weierstrass.X86_64
