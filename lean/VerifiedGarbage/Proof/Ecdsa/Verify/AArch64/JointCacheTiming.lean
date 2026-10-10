import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator

/-! ## `JointBoundaryChecks` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointPrefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p256) := by
  jac_reg_ct [.x0,.x1,.x2,.x3]

theorem jointTail_ct : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256) := by
  jac_field_ct

theorem jointCache_ct : FieldCT (CachedJac.cache cfg.K) := by
  jac_field_ct

theorem jointFinish_ct : FieldCT (Jacobian.jacFinish cfg.K) := by
  jac_field_ct

theorem jointInit_ct : FieldCT (.block (Jacobian.infinity cfg.K cfg.K.R ++ ([.movz .x .x19 256 0] : List Instr))) := by
  jac_field_ct

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointCacheTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.P256Joint Spec.Weierstrass

/-- The cached table and two public recodings, before initializing the accumulator. -/
def JointCachePair (C : Curve) (base T : Addr) (P Q : Point C) (u v : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E s t) ∧
  JointStable cfg C base Q u v s ∧ JointStable cfg C base Q u v t ∧
  JointGenerator cfg C base 8192 P T s ∧ JointGenerator cfg C base 8192 P T t

theorem jointCache_fields {C : Curve} {base : Addr} {E : Nat → Fe C}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) :
    RelCT isa (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (nafLive cfg.K) E)
      (CachedJac.cache cfg.K)
      (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) (runOps CachedInit.ops E)) := by
  apply fieldWP_relCT jointCache_ct
  intro s hi
  refine WP.mono (CachedInit.cache_ok JointLayout.layout.lay JointLayout.layout.aligned hm hi
    (by decide +kernel) (fun _ _ => Low.small (by decide) _) (by decide +kernel)) fun t ⟨hk,it⟩ => ⟨it.sub ?_,hk.sp⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_right _ hx
  · exact List.mem_append_left _ hx

theorem jointCache_relCT {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat} {E : Nat → Fe C}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) :
    RelCT isa (fun s t =>
      FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (nafLive cfg.K) E s t ∧
      NafStable cfg.K C base Q (FastNaf.byte 5 v) s ∧ NafStable cfg.K C base Q (FastNaf.byte 5 v) t ∧
      (∀ j<257,s.mem (off base (cfg.gBits+j))=FastNaf.byte 7 u j) ∧
      (∀ j<257,t.mem (off base (cfg.gBits+j))=FastNaf.byte 7 u j) ∧
      tmv C cfg.K.M.n base s cfg.onep=1 ∧ tmv C cfg.K.M.n base t cfg.onep=1 ∧
      JointGenerator cfg C base 8192 P T s ∧ JointGenerator cfg C base 8192 P T t)
      (CachedJac.cache cfg.K) (JointCachePair C base T P Q u v) := by
  intro s t ts tt s' t' ⟨hp,ps,pt,gs,gt,os,ot,es,et⟩ xs xt
  obtain ⟨he,hp'⟩ := jointCache_fields hm _ _ _ _ _ _ hp xs xt
  obtain ⟨_,_,ys,ks,is,ss⟩ := jointCache_ok JointLayout.layout hm hp.left.to_tmv ps gs os
  obtain ⟨_,_,yt,kt,it,st⟩ := jointCache_ok JointLayout.layout hm hp.right.to_tmv pt gt ot
  obtain ⟨_,rfl⟩ := Exec.det xs ys
  obtain ⟨_,rfl⟩ := Exec.det xt yt
  exact ⟨he,⟨_,hp'⟩,ss,st,
    es.keep ks (Exec.syms xs) (by decide +kernel) (by decide),
    et.keep kt (Exec.syms xt) (by decide +kernel) (by decide)⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
