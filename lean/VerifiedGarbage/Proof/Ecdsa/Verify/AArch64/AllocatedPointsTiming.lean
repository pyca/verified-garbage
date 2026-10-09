import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRunTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsFrame
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyExtra

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

theorem allocatedAfterTable_relCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (JointTablePair base Q u v a b)
      (.seq (CachedJac.cache cfg.K)
        (.seq (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
          (.seq (Joint.run cfg P256Allocated.ops) (Jacobian.jacFinish cfg.K))))
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
  exact RelCT.seq (allocatedRun_timing raw hm hC hc.am3 one hP hQ hu hv) (jointFinish_relCT hc hC)

theorem allocatedPoints_inputCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    {base T : Addr} {P Q : Point p256.C} {u v : Nat} {a b : State}
    (hP : onCurve p256.C P=true) (hQ : onCurve p256.C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (ga : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T a)
    (gb : Weierstrass.AArch64.JointGenerator cfg p256.C base 8192 P T b) :
    RelCT isa (fun s t => s=a ∧ t=b ∧ JacWinPublic p256 base Q v s t ∧
      sv p256 base s U=u ∧ sv p256 base t U=u)
      (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V)) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  change RelCT isa _ (.seq _ (.seq _ (.seq _ _))) _
  apply RelCT.assoc
  apply RelCT.assoc
  exact RelCT.seq (jointPrepTable_relCT Forward.Arithmetic.cases hc hC hQ)
    (allocatedAfterTable_relCT raw hc hC hP hQ hu hv ga gb)

theorem allocatedPointsBody_relCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀) :
    RelCT isa (JointBoundary p256 s₀ t₀) (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V))
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
  exact allocatedPoints_inputCT raw hc hC hc.onG (peerPt_onCurve hc _ _ _) hu hv gs gt
    _ _ _ _ _ _ ⟨rfl,rfl,hp,us,ut⟩ es et


private theorem saveBoundary_relCT {s₀ t₀ : State} :
    RelCT isa (JointBoundary p256 s₀ t₀) (.block P256Allocated.saveExtra)
      (JointBoundary p256 s₀ t₀) := by
  intro s t ts tt s' t' ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,sp⟩ es et
  obtain ⟨_,_,xs,ks,us,_⟩ := allocatedSave_ok ms.scr (by decide)
  obtain ⟨_,_,xt,kt,ut,_⟩ := allocatedSave_ok mt.scr (by decide)
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have hp : AArch64.Taint.Agree (Taint.ofRegs [.x0]) s t := by
    refine ⟨sp,fun r hr => ?_⟩
    have : r=.x0 := by simpa only [Taint.mem_ofRegs,List.mem_singleton] using hr
    subst r
    exact ms.scr.x0.trans mt.scr.x0.symm
  exact ⟨invAllocated_save_ct _ _ _ _ _ _ trivial trivial hp es et,
    pub,⟨gs,mid_saved ms ks us (Exec.syms es)⟩,⟨gt,mid_saved mt kt ut (Exec.syms et)⟩,
    ks.sp.trans (sp.trans kt.sp.symm)⟩

private theorem restorePublic_relCT :
    RelCT isa (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block P256Allocated.restoreExtra)
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hp es et
  refine ⟨invAllocated_restore_ct _ _ _ _ _ _ trivial trivial hp es et,
    (Exec.rdwr es).2.2.trans (hp.1.trans (Exec.rdwr et).2.2.symm),fun r hr => ?_⟩
  have : r=.x0 := by simpa only [Taint.mem_ofRegs,List.mem_singleton] using hr
  subst r
  have keep : ∀i∈instrs (.block P256Allocated.restoreExtra : Prog isa),dstOf i≠some .x0 := by decide
  rw [Exec.gpr keep es,Exec.gpr keep et]
  exact hp.2 _ (by decide)

/-- The allocated points stage preserves the original public-input timing contract,
including the save and restore of its extra working registers. -/
theorem allocatedPoints_relCT (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀) :
    RelCT isa (JointBoundary p256 s₀ t₀) P256Allocated.points
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  rw [P256Allocated.points]
  exact RelCT.seq saveBoundary_relCT
    (RelCT.seq (allocatedPointsBody_relCT raw hc hC hT ps pt) restorePublic_relCT)

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
