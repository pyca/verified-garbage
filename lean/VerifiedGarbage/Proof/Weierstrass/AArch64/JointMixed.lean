import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

theorem jointMixedAdd_ok (certs : Forward.Arithmetic.Cases) {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hnc : Mont.callOf K.M = none)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) (hAff : E q.z=1) :
    WP isa (Joint.mixedAdd K p q o) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  rw [Joint.mixedAdd]
  apply fieldBranch_ok hL hAl hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    have hqz : E q.z ≠ 0 := by rw [hAff]; exact hC.one_ne_zero
    apply WP.seq
    refine WP.mono (jacMixedInit_ok hL hAl hSl ia hV) fun b ⟨kb,ib⟩ => ?_
    apply WP.seq
    refine WP.mono (Forward.Arithmetic.contract certs ib.scr hsize
      ((fprogB_wp _ _ hnc).mpr (jacMixedHead_ok hL hAl hm hA hSl ib hV))) fun c ⟨kc,ic,eh,er⟩ => ?_
    let EH := runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)
    have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
      ((kb.mono (by simp)).trans kc)
    have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacMixedHead_readonly hA E hx
    have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
      rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
      exact hJP
    have oldV : ∀ x ∈ V, x ∈ validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
    apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
    · intro d id kd hz
      have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using eh.symm.trans hz
      apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
      · intro e ie ke hrz
        have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using er.symm.trans hrz
        have hpq := hJP.same hC hJQ hpz hqz hx hy
        have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        rw [←hpq]
        refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl hnc hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
        exact (JacPost.sub ⟨_,kt,it,jt⟩ oldV).prefix
          (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro e ie ke hrz
        have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := by
          intro he
          apply hrz
          rw [er]
          simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
        have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
        rw [hadd]
        refine WP.mono (infinityPoint_ok hL hAl
          (fun x hx => hSl x (by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
        exact (JacPost.sub ht oldV).prefix
          (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
    · intro d id kd hz
      have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := by
        intro he
        apply hz
        rw [eh]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      refine WP.mono (Forward.Arithmetic.contract certs id.scr hsize
        ((fprogB_wp _ _ hnc).mpr (jacMixedTail_ok hL hAl hm hA hSl id hV))) fun t ⟨kt,it,ht⟩ => ?_
      have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
      dsimp only at jt
      rw [hAff,←ht] at jt
      exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64
