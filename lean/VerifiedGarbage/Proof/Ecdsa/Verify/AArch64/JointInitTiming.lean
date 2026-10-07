import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCacheTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.P256Joint Spec.Weierstrass

private theorem jointInit_fields {C : Curve} {base : Addr} {E : Nat → Fe C}
    (hOne : cfg.K.one<C.p) :
    RelCT isa (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E)
      (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
      (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg)
        (infinityEnv cfg.K.M C.p cfg.K.one E cfg.K.R)) := by
  apply fieldWP_relCT jointInit_ct
  intro s hi
  have hR := wordsVal_lt s.mem base cfg.K.M.mo cfg.K.M.n
  rw [hi.mod.val] at hR
  have h0 : 0<C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have slots : ∀ x∈[cfg.K.R.x,cfg.K.R.y,cfg.K.R.z],x∈jointSlots cfg := by decide +kernel
  rw [WP.block_append_iff]
  have iw : WP isa (.block (Jacobian.infinity cfg.K cfg.K.R)) s fun t =>
      Inv cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg)
        (infinityEnv cfg.K.M C.p cfg.K.one E cfg.K.R) t ∧ t.sp=s.sp := by
    rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
    refine WP.mono (setField_ok JointLayout.layout.lay JointLayout.layout.aligned hi
      (slots _ (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (setField_ok JointLayout.layout.lay JointLayout.layout.aligned ia
      (slots _ (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
    refine WP.mono (setField_ok JointLayout.layout.lay JointLayout.layout.aligned ib
      (slots _ (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
    exact ⟨it.sub (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hx))),kt.sp.trans (kb.sp.trans ka.sp)⟩
  refine WP.mono iw fun a ⟨ia,sp⟩ => ?_
  refine WP.mono (jointInitCounter_ok a) fun t ⟨_,kt⟩ =>
    ⟨ia.of_keeps kt (by decide),kt.sp.trans sp⟩

/-- Initialization establishes a common point and public counter in both runs. -/
theorem jointInit_relCT {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hOne : cfg.K.one<C.p) :
    RelCT isa (JointCachePair C base T P Q u v)
      (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
      (JointPair cfg C base 8192 (JointCore cfg C base 8192 Q u v
        (JointGenerator cfg C base 8192 P T)) .infinity 256) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,ss,st,gs,gt⟩ es et
  obtain ⟨he,hp'⟩ := jointInit_fields hOne _ _ _ _ _ _ hp es et
  obtain ⟨_,_,xs,_,cs,s19⟩ := jointInit_ok hOne hp.left.to_tmv ss gs
  obtain ⟨_,_,xt,_,ct,t19⟩ := jointInit_ok hOne hp.right.to_tmv st gt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,⟨_,hp'⟩,cs,ct,s19,t19⟩

end VG.Proof.Ecdsa.Verify.AArch64
