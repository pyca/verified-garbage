import VerifiedGarbage.Proof.Weierstrass.X86_64.JacDouble
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField

/-! The exceptional equal-point branch uses the same forwarded field compiler. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem jacDoubleForward_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o++rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR S p p,x∈V) {P : Point C}
    (hP : onCurve C P=true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (ForwardField.programB M (dblJMul S p o)) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t ∧
      InvJ C (runOps (dblJMul S p o) E o.x) (runOps (dblJMul S p o) E o.y)
        (runOps (dblJMul S p o) E o.z) (Spec.Weierstrass.add P P) := by
  have he : dblJMul S p o=ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
  rw [he]
  have hN := dblJChoiceN_ok true
  refine WP.mono (ForwardField.programB_ok hn hL hm _ hI
    (fun op hop x hx => hSl x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk hN S p p o) hV)) fun t ⟨kt,it⟩ => ⟨kt.mono ?_,it.sub ?_,?_⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    exact ofN_out hN op hop
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · apply InvJ.dbl' hC ha hP hJ
    exact (congrArg₂ Prod.mk (ofN_run hN hA E 6)
      (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))).trans
        (dblJChoiceN_run true _)

end VG.Proof.Weierstrass.X86_64
