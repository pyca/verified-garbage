module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNaf9Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCachedDigitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Inplace
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCachedDigitTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointPairedTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Inplace
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! ## `JointChecks` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointMixed_checks : JointMixedChecks P256Joint.cfg.K P256Joint.cfg.K.R
    P256Joint.cfg.K.E P256Joint.cfg.K.D where
  zero := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> jac_field_ct
  copyQ := by jac_field_ct
  init := by jac_field_ct
  head := Forward.ArithmeticMixedHead.ct
  tail := Forward.ArithmeticMixedTail.ct
  double := Forward.rd_ct
  infinity := by jac_field_ct

theorem jointFixed_checks : JointFixedChecks P256Joint.cfg where
  lookup := VG.Taint.constantTime (A:=taintS [P256Joint.cfg.tsym]) (Taint.ofRegs [.x0,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)
  sign := by jac_reg_ct [.x0,.x19]
  neg := by jac_field_ct
  read := by jac_reg_ct [.x0,.x19]
  mixed := jointMixed_checks
  copy := by jac_field_ct

theorem jointGPrep_checks : FastPrep9Checks P256Joint.cfg.G (p256.sl U) where
  init := by jac_reg_ct [.x0]
  step := by jac_reg_ct [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x20]

theorem jointQPrep_checks : FastPrepChecks P256Joint.cfg.K (p256.sl V) 5 where
  init := by jac_reg_ct [.x0]
  step := by jac_reg_ct [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x20]

theorem cachedDigit_checks : CachedField.DigitChecks where
  entry := { lookup := by jac_reg_ct [.x0,.x2]
             sign := by jac_reg_ct [.x0,.x19]
             neg := by jac_field_ct }
  add := cachedAdd_checks
  copy := by jac_field_ct
  digit := by jac_reg_ct [.x0,.x19]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedRunTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem allocatedOps_timing (raw : RawCorrect) {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hOne : K.one<C.p) :
    JointOpsTiming cfg P256Allocated.ops C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) where
  double := by
    intro A j E
    dsimp only [P256Allocated.ops]
    have h := fieldWP_relCT (base:=base) (V:=jointLive cfg) (V':=jointLive cfg) (E:=E)
      Proof.P256.EcdhDouble.Certificate.ct fun _ hi =>
        WP.mono (double_field_ok hi) fun _ ⟨hk,it⟩ => ⟨it,hk.regs.sp⟩
    exact h.mono (fun _ _ h => h.1) (fun _ _ h => ⟨_,h⟩)
  peer := by
    intro A j hj E
    exact (cachedDigit_relCT raw (base:=base) (E:=E) hm hOne hj cachedDigit_checks).mono
      (fun _ _ h => ⟨h.1,h.2.1.stable,h.2.2.1.stable,h.2.2.2⟩) (fun _ _ h => h)
  generator := by
    intro A j hj E
    exact fixedDigit_relCT raw hC hm hOne hj jointFixed_checks

theorem allocatedRun_timing (raw : RawCorrect) {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : K.one<C.p) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) :
    RelCT isa (JointPair cfg C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) .infinity 256)
      (Joint.run cfg P256Allocated.ops)
      (JointPair cfg C base 8192
        (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T))
        (add (mul u P) (mul v Q)) 0) :=
  allocatedJointPair_run hC hP hQ hu hv (ops_ok raw hC ha hm hOne hP hQ)
    (allocatedOps_timing raw hm hC hOne) (by jac_reg_ct [.x19])

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `JointRunTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open P256Joint

theorem jointOps_timing {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) (hC : Law C) (hOne : cfg.K.one<C.p) :
    JointOpsTiming cfg ops C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) where
  double := by
    intro A j E
    dsimp only [ops]
    have h := Forward.Arithmetic.double_relCT (S:=cfg.K.S) (p:=cfg.K.R) Forward.Arithmetic.cases
      (base:=base) (E:=E) JointLayout.layout.lay JointLayout.layout.aligned hm (by decide)
      (by decide +kernel) (Low.small (by decide) _) (jointLive_R cfg) Forward.ArithmeticRR.ct
    exact h.mono (fun _ _ h => h.1) (fun _ _ h => ⟨_,h⟩)
  peer := by
    intro A j hj E
    exact (CachedField.digit_relCT (base:=base) (E:=E) JointLayout.layout (by decide) hm hOne hj cachedDigit_checks).mono
      (fun _ _ h => ⟨h.1,h.2.1.stable,h.2.2.1.stable,h.2.2.2⟩) (fun _ _ h => h)
  generator := by
    intro A j hj E
    exact jointFixedDigit_relCT Forward.Arithmetic.cases JointLayout.fixedLayout hC hm (by decide) hOne hj jointFixed_checks

theorem jointRun_timing {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : cfg.K.one<C.p) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) :
    RelCT isa (JointPair cfg C base 8192
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) .infinity 256)
      (Joint.run cfg ops)
      (JointPair cfg C base 8192
        (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T))
        (add (mul u P) (mul v Q)) 0) := by
  exact jointPair_run hC hP hQ hu hv (jointOps_ok hm hC ha hOne hP hQ)
    (jointOps_timing hm hC hOne) (by jac_reg_ct [.x19])

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointFinishTiming` -/

section

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
  have hone : toM p256.C.p (2^(64*cfg.K.M.n)) cfg.K.one=1 := toM_cmont hc.toBaseCfgOk 1
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

end
