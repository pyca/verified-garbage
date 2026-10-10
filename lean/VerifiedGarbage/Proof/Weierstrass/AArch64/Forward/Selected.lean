import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Impl.P256.VerifyDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeOk

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
namespace Fixed
open VG.Impl.P256.VerifyDouble

def original (p o : Pt) := fprog M (dblJMul S p o)
def optimized (p o : Pt) := VG.Impl.Weierstrass.AArch64.Forward.optimize (original p o)

structure Case (p o : Pt) where
  checked : OptChecked 8192 (original p o) (optimized p o)
  leftBound : ∀ i∈original p o,instrBound i≤992
  rightBound : ∀ i∈optimized p o,instrBound i≤992
  clob : ∀ r∈(optimized p o).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n

structure Cases where
  rd : Case R D
  dr : Case D R
  ed : Case E D

 theorem Case.refine {p o : Pt} (c : Case p o) {base : Addr} {size : Nat} {s : State}
    (hs : Scr s base size) (hsize : 992≤size) {Q : State → Prop}
    (hnc : Mont.callOf M = none) (hq : WP isa (fprogB M (dblJMul S p o)) s Q) :
    WP isa (VG.Impl.Weierstrass.AArch64.Forward.double M S p o) s fun t =>
      ∃ u,Q u ∧ t.mem=u.mem ∧ KeepRegs (VG.Proof.Mont.AArch64.clob M.n) s t := by
  have h := c.checked.refine (by decide) (by decide) hs
    (fun i hi => Nat.le_trans (c.leftBound i hi) hsize)
    (fun i hi => Nat.le_trans (c.rightBound i hi) hsize) ((fprogB_wp _ _ hnc).mp hq)
  exact WP.mono h fun t ⟨u,hu,hm,hk⟩ => ⟨u,hu,hm,hk.mono c.clob⟩

end Fixed

 theorem selected_refinement (certs : Fixed.Cases) {M : VG.Impl.Mont.Mod}
    {S : RcbSlots} {p o : Pt} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (sel : VG.Impl.P256.VerifyDouble.selected M S p o)
    (hL : Lay M size Sl) (hSl : ∀ x∈rcbW S o ++ rcbR S p p,Sl x)
    {s : State} (hs : Scr s base size) {Q : State → Prop}
    (hq : WP isa (fprogB M (dblJMul S p o)) s Q) :
    WP isa (VG.Impl.P256.VerifyDouble.double M S p o) s fun t =>
      ∃ u,Q u ∧ t.mem=u.mem ∧ KeepRegs (VG.Proof.Mont.AArch64.clob M.n) s t := by
  rw [VG.Impl.P256.VerifyDouble.double,ite_eq_left sel]
  obtain ⟨rfl,rfl,hpo⟩ := sel
  have hslot : Sl VG.Impl.P256.VerifyDouble.S.t5 := hSl _ (by simp [rcbW])
  have hsize : 992≤size := hL.le _ hslot
  rcases hpo with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact certs.rd.refine hs hsize (callOf_small (by decide)) hq
  · exact certs.dr.refine hs hsize (callOf_small (by decide)) hq
  · exact certs.ed.refine hs hsize (callOf_small (by decide)) hq

theorem double_ok (certs : Fixed.Cases) {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    WP isa (VG.Impl.P256.VerifyDouble.double M S p o) s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t ∧
      InvJ C (runOps (dblJMul S p o) E o.x) (runOps (dblJMul S p o) E o.y)
        (runOps (dblJMul S p o) E o.z) (Spec.Weierstrass.add P P) := by
  by_cases sel : VG.Impl.P256.VerifyDouble.selected M S p o
  · apply double_of_refinement hL hAl hm hC ha hA hSl (.inl hnc) hI hV hP hJ
    intro Q hq
    exact selected_refinement certs sel hL hSl hI.scr hq
  · rw [VG.Impl.P256.VerifyDouble.double,ite_eq_right sel]
    exact jacDouble_ok hL hAl hm hC ha hA hSl (.inl hnc) hI hV hP hJ

theorem double_multiple_ok (certs : Fixed.Cases) {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V W : List Nat} (hW : ∀ x ∈ rcbW S o, x ∈ W)
    {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C} {e : Nat}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) (mul e P)) :
    WP isa (VG.Impl.P256.VerifyDouble.double M S p o) s fun t =>
      ∃ E', ProgKeep M base W s t ∧ Inv M base size C.p Sl V E' t ∧
      InvJ C (E' o.x) (E' o.y) (E' o.z) (mul (2*e) P) := by
  refine WP.mono (double_ok certs hL hAl hnc hm hC ha hA hSl hI hV (hC.onCurve_mul hP e) hJ)
    fun t ⟨hk,hi,hj⟩ => ⟨_,hk.mono hW,hi.sub (fun _ hx => List.mem_append_right _ hx),?_⟩
  rw [hC.add_mul_mul hP,show e+e=2*e by omega] at hj
  exact hj

end VG.Proof.Weierstrass.AArch64.Forward
