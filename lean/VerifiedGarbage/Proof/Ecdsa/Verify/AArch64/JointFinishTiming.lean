import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointBoundaryChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointRunTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open P256Joint

theorem jointFinish_relCT (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q A : Point p256.C} {u v j : Nat} :
    RelCT isa (JointPair cfg p256.C base 8192
      (JointCore cfg p256.C base 8192 Q u v (JointGenerator cfg p256.C base 8192 P T)) A j)
      (Jacobian.jacFinish cfg.K) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,_,_⟩ es et
  have hm : UnitMod p256.C.p (2^(64*cfg.K.M.n)) := unitMod_pow_two hc.p_odd _
  have one : cfg.K.one<p256.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hone : toM p256.C.p (2^(64*cfg.K.M.n)) cfg.K.one=1 := toM_cmont hc 1
  obtain ⟨_,_,xs,ks,us,ms,ls,rs⟩ := jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl)
    hm hC one hone (by decide) cs
  obtain ⟨_,_,xt,kt,ut,mt,lt,rt⟩ := jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl)
    hm hC one hone (by decide) ct
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  refine ⟨jointFinish_ct _ _ _ _ _ _ trivial trivial hp.public es et,
    ks.sp.trans (hp.sp.trans kt.sp.symm),fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
  subst hr
  rw [ks.gpr _ (by decide),kt.gpr _ (by decide)]
  exact hp.left.scr.x0.trans hp.right.scr.x0.symm

end VG.Proof.Ecdsa.Verify.AArch64
