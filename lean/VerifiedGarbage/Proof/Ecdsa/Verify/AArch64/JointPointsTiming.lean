import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointFinishTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGeneratorFrame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInputTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointBoundaryGenerator

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open P256Joint

theorem jointAfterTable_relCT (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (JointTablePair base Q u v a b)
      (.seq (CachedJac.cache cfg.K)
        (.seq (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
          (.seq (Joint.run cfg ops) (Jacobian.jacFinish cfg.K))))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have hm : UnitMod p256.C.p (2^(64*cfg.K.M.n)) := unitMod_pow_two hc.p_odd _
  have one : cfg.K.one<p256.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
  have cache : RelCT isa (JointTablePair base Q u v a b) (CachedJac.cache cfg.K)
      (JointCachePair p256.C base T P Q u v) := by
    intro s t ts tt s' t' h es et
    have ⟨gs,gt⟩ := h.generators ga gb
    obtain ⟨E,hp,_,_,_,_,_,_,ps,pt⟩ := h
    exact jointCache_relCT hm _ _ _ _ _ _
      ⟨hp,ps.stable,pt.stable,ps.generator,pt.generator,ps.one,pt.one,gs,gt⟩ es et
  apply RelCT.seq cache
  apply RelCT.seq (jointInit_relCT one)
  exact RelCT.seq (jointRun_timing hm hC hc.am3 one hP hQ hu hv) (jointFinish_relCT hc hC)

theorem jointPoints_inputCT (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (fun s t => s=a ∧ t=b ∧ JacWinPublic p256 base Q v s t ∧
      sv p256 base s U=u ∧ sv p256 base t U=u)
      P256Joint.points (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  change RelCT isa _ (.seq _ (.seq _ (.seq _ _))) _
  apply RelCT.assoc
  apply RelCT.assoc
  exact RelCT.seq (jointPrepTable_relCT Forward.Arithmetic.cases hc hC hQ)
    (jointAfterTable_relCT hc hC hP hQ hu hv ga gb)

/-- The complete joint points stage depends only on the original public inputs. -/
theorem jointPoints_relCT (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀) :
    RelCT isa (JointBoundary p256 s₀ t₀) P256Joint.points
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hb es et
  obtain ⟨hp,us,ut⟩ := jointBoundary_input hc hC hb
  obtain ⟨gs,gt⟩ := jointBoundary_generators hc hC hT ps pt hb
  have hu : publicU p256 s₀<2^256 := by
    rw [←us]
    exact wordsVal_lt s.mem (s₀.gpr .x3) (p256.sl U) 4
  have hv : publicV p256 s₀<2^256 := by
    rw [←hp.left.scalar]
    exact wordsVal_lt s.mem (s₀.gpr .x3) (p256.sl V) 4
  exact jointPoints_inputCT hc hC hc.onG (peerPt_onCurve hc _ _ _) hu hv gs gt
    _ _ _ _ _ _ ⟨rfl,rfl,hp,us,ut⟩ es et

end VG.Proof.Ecdsa.Verify.AArch64
