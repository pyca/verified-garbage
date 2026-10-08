import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.JacDouble

/-! In-place doubling for the secret-scalar Jacobian window loop. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def dblN : List FOp := dblJMul ⟨9,10,0,1,2,3,4,5⟩ ⟨6,7,8⟩ ⟨6,7,8⟩
def dblσ (S : RcbSlots) (p : Pt) (i : Nat) : Nat := (rcbW S p).getD i S.a

theorem dbl_eq (S : RcbSlots) (p : Pt) : dblJMul S p p = dblN.map (FOp.rename (dblσ S p)) := rfl

theorem dblN_out : ∀ op∈dblN,op.out<9 := by decide

theorem dblN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblN e 6,runOps dblN e 7,runOps dblN e 8)=dblJF (e 6) (e 7) (e 8) := by
  dsimp only [dblN,dblJMul,runOps,List.foldl,FOp.run,Function.update]
  simp only [dblJF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem dbl_run {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p : Pt}
    (hN : (rcbW S p).Nodup) (ha : S.a∉rcbW S p) (e : Nat → F) :
    (runOps (dblJMul S p p) e p.x,runOps (dblJMul S p p) e p.y,
      runOps (dblJMul S p p) e p.z)=dblJF (e p.x) (e p.y) (e p.z) := by
  rw [dbl_eq]
  have inj {w : Nat} (hw : w<9) (y : Nat) (he : dblσ S p y=dblσ S p w) : y=w :=
    getD_append_inj (R:=[]) hN (by simp) ha hw y (by simpa only [List.append_nil,dblσ] using he)
  have he := runOps_rename (dblσ S p) dblN e (fun op hop => inj (dblN_out op hop))
  exact (congrArg₂ Prod.mk (congrFun he 6)
    (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans (dblN_run (fun i => e (dblσ S p i)))

theorem dbl_ok {K : JacWinCfg} {base : Addr} {size wk : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hW : WkOk K.F K.M C.p size wk Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {p : Pt} (hN : (rcbW K.S p).Nodup) (hA : K.S.a∉rcbW K.S p)
    (hSl : ∀ x∈rcbW K.S p,Sl x) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x∈[p.x,p.y,p.z],x∈V)
    {P : Point C} (hP : onCurve C P=true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (K.dbl p) s fun t => ProgKeep K.M base wk (rcbW K.S p) s t ∧
      Inv K.M base size C.p Sl ([p.x,p.y,p.z]++V) (runOps (dblJMul K.S p p) E) t ∧
      InvJ C (runOps (dblJMul K.S p p) E p.x) (runOps (dblJMul K.S p p) E p.y)
        (runOps (dblJMul K.S p p) E p.z) (Spec.Weierstrass.add P P) := by
  have hs : ∀ op∈dblJMul K.S p p,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [dblJMul,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
      rcases hx with rfl|rfl|rfl <;> exact hSl _ (by simp [rcbW])
  have hr : readsOk (dblJMul K.S p p) V=true := by
    rw [dbl_eq]
    exact readsOk_mono (readsOk_rename (dblσ K.S p)
      (show readsOk dblN [6,7,8]=true by decide)) hV
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr) fun t ⟨kt,it⟩ => ⟨kt.mono ?_,it.sub ?_,?_⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    simp only [dblJMul,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [FOp.out,rcbW]
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [dblJMul,FOp.out]
    · exact Or.inl hx
  · exact InvJ.dbl' hC ha hP hJ (dbl_run hN hA E)

end VG.Proof.Weierstrass.X86.JWin
