import VerifiedGarbage.Proof.Weierstrass.X86.Rcb3
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! Direct-product Jacobian doubling for the public verification loops. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

/-- The doubled point stays Jacobian; there is no coordinate conversion
between consecutive doublings. -/
theorem jacDouble_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size wk : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk F M C.p size wk Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprog F (dblJMul S p o)) s fun t =>
      ProgKeep M base wk (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t ∧
      InvJ C (runOps (dblJMul S p o) E o.x) (runOps (dblJMul S p o) E o.y)
        (runOps (dblJMul S p o) E o.z) (Spec.Weierstrass.add P P) := by
  have he : dblJMul S p o = ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
  rw [he]
  refine WP.mono (ofN_ok hL hW hm (dblJChoiceN_ok true) hA hSl hI hV)
    fun t ⟨hk,hi,hv⟩ => ⟨hk,hi,?_⟩
  exact InvJ.dbl' hC ha hP hJ (hv.trans (dblJChoiceN_run true _))

end VG.Proof.Weierstrass.X86
