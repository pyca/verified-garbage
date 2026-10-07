import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint

/-! Canonical affine generator coordinates and their external read-only storage. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

structure JointGeneratorRow (C : Curve) (G : Point C) where
  x : Nat → Nat
  y : Nat → Nat
  canonical : ∀ a,1≤a → a≤63 → a%2=1 → x a<C.p ∧ y a<C.p
  point : ∀ a,1≤a → a≤63 → a%2=1 →
    InvJ C (toM C.p (2^256) (x a)) (toM C.p (2^256) (y a)) 1 (mul a G)

def JointGenerator (c : Joint.Cfg) (C : Curve) (base T : Addr) (size : Nat)
    {G : Point C} (row : JointGeneratorRow C G) (s : State) : Prop :=
  ∀ a,1≤a → a≤63 → a%2=1 → FixedSource base T c.tsym size a (row.x a) (row.y a) s

theorem JointGenerator.keep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {row : JointGeneratorRow C G} {s t : State} {W : List Nat}
    (h : JointGenerator c C base T size row s) (hk : ProgKeep c.K.M base W s t)
    (hs : t.syms=s.syms) (hw : ∀ w∈W,w+8*c.K.M.n≤size) (htmp : c.K.M.tmp+8*c.K.M.n≤size) :
    JointGenerator c C base T size row t := fun a ha hb ho => (h a ha hb ho).keep hk hs hw htmp

theorem JointGenerator.workKeep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {row : JointGeneratorRow C G} (hL : JointLayout c size)
    (htmp : c.K.M.tmp+8*c.K.M.n≤size) :
    ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms →
      JointGenerator c C base T size row s → JointGenerator c C base T size row t := by
  intro s t hk hs h
  apply h.keep hk hs _ htmp
  intro w hw
  apply hL.lay.le w
  simp only [jointWork,jointSlots,nafSlots,List.mem_append] at hw ⊢
  grind

theorem jointFixedEntry_core_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {row : JointGeneratorRow C G} {s : State}
    (hL : JointLookupLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^256) c.K.one=1)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s)
    (hmag : FastNaf.magnitude 7 u j≠0) (h8 : s.gpr .r8=(FastNaf.byte 7 u j).setWidth 64) :
    WP isa (Joint.fixedEntry c.K c.tsym) s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) A t ∧
      Inv c.K.M base size C.p (·∈jointSlots c) (jacCoords c.K.E++jointLive c) (tmv C c.K.M.n base t) t ∧
      InvJ C (tmv C c.K.M.n base t c.K.E.x) (tmv C c.K.M.n base t c.K.E.y)
        (tmv C c.K.M.n base t c.K.E.z) (FastNaf.point C G 7 u j) ∧
      tmv C c.K.M.n base t c.K.E.z=1 := by
  have ha : 1≤FastNaf.magnitude 7 u j := by omega
  have hb : FastNaf.magnitude 7 u j≤63 := FastNaf.magnitude_le (Or.inr rfl) u j
  have ho := (FastNaf.magnitude_odd_or_zero 7 u j).resolve_left hmag
  have hd : ∀ x∈jacCoords c.K.E,x∈jointSlots c := by
    intro x hx
    simp only [jointSlots,nafSlots,jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hw : ∀ x∈jacCoords c.K.E,x∈jointWork c := by
    intro x hx
    simp only [jointWork,jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hzero : c.K.zero∉jacCoords c.K.E := fun hx => hL.zeroApart (List.mem_append_left _ hx)
  refine WP.mono_syms (jointFixedFast_ok hL.layout.lay hL.layout.n hm h.field hmag h8
    (h.external _ ha hb ho) hL.exy hL.exz hd (row.canonical _ ha hb ho).1
    (row.canonical _ ha hb ho).2 hOne hOneVal (by simp [jointLive,winRo]) h.stable.zero hzero
    (row.point _ ha hb ho)) fun t ⟨kt,it,pt,zt⟩ st => ?_
  have kw := kt.mono hw
  have ht := JointGenerator.workKeep hL.layout h.field.mod.tmp s t kw st h.external
  refine ⟨kw,h.of_write hL.layout kt hw hd
    (fun x hx hn => hL.accumApart x hx (List.mem_append_left _ hn))
    (it.sub (fun _ hx => List.mem_append_right _ hx)) ht,it.to_tmv,
    it.point_tmv (fun _ hx => List.mem_append_left _ hx) pt,?_⟩
  unfold tmv
  rw [it.val _ (by simp [jacCoords]),zt]

end VG.Proof.Weierstrass.X86_64
