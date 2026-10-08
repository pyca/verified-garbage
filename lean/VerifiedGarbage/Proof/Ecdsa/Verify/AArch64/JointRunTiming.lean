import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointWindow
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointChecks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR

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
