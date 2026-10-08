import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-! Direct-product Jacobian doubling for the public verification loops. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

/-- The doubled point stays Jacobian; there is no coordinate conversion
between consecutive doublings. -/
theorem jacDouble_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprogB M (dblJMul S p o)).inline s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t ∧
      InvJ C (runOps (dblJMul S p o) E o.x) (runOps (dblJMul S p o) E o.y)
        (runOps (dblJMul S p o) E o.z) (Spec.Weierstrass.add P P) := by
  have he : dblJMul S p o = ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
  rw [he]
  refine WP.mono (ofN_ok hL hm (dblJChoiceN_ok true) hA hSl hI hV)
    fun t ⟨hk,hi,hv⟩ => ⟨hk,hi,?_⟩
  exact InvJ.dbl' hC ha hP hJ (hv.trans (dblJChoiceN_run true _))

end VG.Proof.Weierstrass.X86_64
