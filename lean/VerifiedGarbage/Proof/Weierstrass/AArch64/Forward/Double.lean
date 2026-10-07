import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem transfer_post {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E : Nat → Fin m} {s u t : State}
    (hm : t.mem=u.mem) (hk : KeepRegs (clob M.n) s t)
    (hku : ProgKeep M base W s u) (hu : Inv M base size m Sl V E u) :
    ProgKeep M base W s t ∧ Inv M base size m Sl V E t := by
  have kt : ProgKeep M base W s t :=
    ⟨hk.gpr,hk.rd,hk.wr,hk.sp,fun x hx ht => hm ▸ hku.mem x hx ht⟩
  have sx : s.gpr .x0=base := (hku.gpr _ (x0_not_clob' _)).symm.trans hu.scr.x0
  have sw : ⟨base,size⟩∈s.wr := hku.wr ▸ hu.scr.wr
  have scr : Scr s base size := ⟨sx,sw,hu.scr.nowrap,hu.scr.enc⟩
  exact ⟨kt,kt.scr scr,hm ▸ hu.mod,hu.sl,fun x hx => hm ▸ hu.lt x hx,
    fun x hx => hm ▸ hu.val x hx⟩

/-- Any checked memory-preserving replacement of the double's field block
inherits the existing algebraic proof and its unchanged field contract. -/
theorem double_of_refinement {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P)
    {code : Prog isa}
    (hr : ∀ Q : State → Prop,WP isa (fprogB M (dblJMul S p o)) s Q →
      WP isa code s fun t => ∃ u,Q u ∧ t.mem=u.mem ∧ KeepRegs (clob M.n) s t) :
    WP isa code s fun t =>
      ProgKeep M base (rcbW S o) s t ∧
      Inv M base size C.p Sl ([o.x,o.y,o.z]++V) (runOps (dblJMul S p o) E) t ∧
      InvJ C (runOps (dblJMul S p o) E o.x) (runOps (dblJMul S p o) E o.y)
        (runOps (dblJMul S p o) E o.z) (Spec.Weierstrass.add P P) := by
  apply WP.mono (hr _ (jacDouble_ok hL hAl hm hC ha hA hSl hI hV hP hJ))
  rintro t ⟨u,⟨hku,hu,hju⟩,hmem,hk⟩
  obtain ⟨kt,it⟩ := transfer_post hmem hk hku hu
  exact ⟨kt,it,hju⟩

end VG.Proof.Weierstrass.AArch64.Forward
