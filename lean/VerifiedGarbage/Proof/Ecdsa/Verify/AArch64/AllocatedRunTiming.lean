import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCachedDigitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointPairedTiming

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
    have h := field_relCT raw Proof.P256.VerifyAllocated.Double.caseProof
      (base:=base) (V:=jointLive cfg) (Out:=jointLive cfg) (E:=E)
      (by decide +kernel) (by decide +kernel)
      (fun _ hx => (mem_validAfter _ _).mpr (Or.inl hx))
      (by decide +kernel) Proof.P256.VerifyAllocated.Double_ct
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
