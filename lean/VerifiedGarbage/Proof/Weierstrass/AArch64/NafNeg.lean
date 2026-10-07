import VerifiedGarbage.Proof.Weierstrass.AArch64.NafCore

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem nafNeg_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈[K.E.x,K.E.y,K.E.z,K.zero],x∈V)
    (hxy : K.E.x≠K.E.y) (hzy : K.E.z≠K.E.y) (hz : E K.zero=0)
    {P : Point C} (hp : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) P) :
    WP isa (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y)) s fun t =>
      ProgKeep K.M base [K.E.y] s t ∧
      Inv K.M base size C.p Sl V (Function.update E K.E.y (-E K.E.y)) t ∧
      InvJ C ((Function.update E K.E.y (-E K.E.y)) K.E.x)
        ((Function.update E K.E.y (-E K.E.y)) K.E.y)
        ((Function.update E K.E.y (-E K.E.y)) K.E.z) (negPt P) := by
  have hs : ∀ x∈(FOp.sub K.E.y K.zero K.E.y).out::(FOp.sub K.E.y K.zero K.E.y).ins,Sl x := by
    intro x hx; apply hi.sl x; apply hV x
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hv : ∀ x∈(FOp.sub K.E.y K.zero K.E.y).ins,x∈V := by
    intro x hx; apply hV x
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono (fop_ok hL hAl hm hi hs hv) fun t ⟨kt,it⟩ => ?_
  have he : FOp.run (.sub K.E.y K.zero K.E.y) E=Function.update E K.E.y (-E K.E.y) := by
    simp only [FOp.run,hz]; congr 1
  rw [he] at it
  refine ⟨progKeep_of_op kt (by simp [FOp.out]),it.sub (fun _ hx => List.mem_cons_of_mem _ hx),?_⟩
  simpa only [Function.update_of_ne hxy,Function.update_of_ne hzy,Function.update_self] using hp.negY

end VG.Proof.Weierstrass.AArch64
