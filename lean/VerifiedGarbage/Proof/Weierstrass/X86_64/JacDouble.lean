module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Jac

/-! Direct-product Jacobian doubling for the public verification loops. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

/-- The doubled point stays Jacobian; there is no coordinate conversion
between consecutive doublings. Any doubling of `C` (`JDblOk`): `dblJMul`
for `a = -3`. -/
theorem jacDouble_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {dbl : RcbSlots → Pt → Pt → List FOp} (hd : JDblOk C dbl)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (fprogB M (dbl S p o)).inline s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dbl S p o) E) t ∧
      InvJ C (runOps (dbl S p o) E o.x) (runOps (dbl S p o) E o.y)
        (runOps (dbl S p o) E o.z) (Spec.Weierstrass.add P P) := by
  obtain ⟨N, hN, he, hD⟩ := hd
  rw [he]
  refine WP.mono (ofN_ok hL hm hN hA hSl hI hV) fun t ⟨hk,hi,hv⟩ => ⟨hk,hi,?_⟩
  simp only [Prod.mk.injEq] at hv
  rw [hv.1, hv.2.1, hv.2.2]
  exact hD _ hP hJ

end VG.Proof.Weierstrass.X86_64
