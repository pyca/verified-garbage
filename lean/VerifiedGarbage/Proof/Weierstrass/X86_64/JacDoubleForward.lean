module
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Proof.Weierstrass.JacMul
import Batteries.Logic

/-! The exceptional equal-point branch uses the same forwarded field compiler. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

/-- Any doubling of `C` (`JDblOk`), forwarded. -/
theorem jacDoubleForward_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {dbl : RcbSlots → Pt → Pt → List FOp} (hd : JDblOk C dbl)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o++rcbR S p p,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR S p p,x∈V) {P : Point C}
    (hP : onCurve C P=true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (ForwardField.programB M (dbl S p o)).inline s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dbl S p o) E) t ∧
      InvJ C (runOps (dbl S p o) E o.x) (runOps (dbl S p o) E o.y)
        (runOps (dbl S p o) E o.z) (Spec.Weierstrass.add P P) := by
  obtain ⟨N, hN, he, hD⟩ := hd
  rw [he]
  refine WP.mono (ForwardField.programB_ok hL hm _ hI
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
  · rw [show o.x = rcbσ S p p o 6 from rfl, show o.y = rcbσ S p p o 7 from rfl,
      show o.z = rcbσ S p p o 8 from rfl, ofN_run hN hA E 6, ofN_run hN hA E 7, ofN_run hN hA E 8]
    exact hD _ hP hJ

end VG.Proof.Weierstrass.X86_64
