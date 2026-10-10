import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Inplace
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

private abbrev cfg := P256Joint.cfg

/-- The public generator table is outside the scratch region. -/
theorem jointExternal_frame {C : Curve} {base T : Addr} {G : Point C} :
    CachedField.ExternalFrame base (JointGenerator cfg C base 8192 G T) := by
  intro s t hk hsym hs
  exact hs.keep hk hsym (by decide +kernel) (by decide)

theorem jointOps_ok {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : cfg.K.one<C.p) (hP : onCurve C P=true) (hQ : onCurve C Q=true) :
    JointOpsOk cfg P256Joint.ops C base (jointWork cfg)
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) P Q u v where
  keep := by
    intro A s t hk hsym hs
    apply hs.of_keeps hk (by decide)
    exact { symbol := by rw [hsym]; exact hs.external.symbol
            read := by simpa only [hk.rd,hk.wr] using hs.external.read
            outside := hs.external.outside
            bounds := by simpa only [hk.mem] using hs.external.bounds
            point := by simpa only [hk.mem] using hs.external.point }
  double := by
    intro A s hA hs
    dsimp only [P256Joint.ops]
    refine WP.mono_syms (Forward.Arithmetic.double_ok (S:=cfg.K.S) Forward.Arithmetic.cases
      JointLayout.layout.lay JointLayout.layout.aligned hm (by decide) hC ha
      (by decide +kernel) (by decide +kernel) (Low.small (by decide) _) hs.field (jointLive_R cfg) hA hs.point)
      fun t ⟨hk,hi,hj⟩ hsym => ?_
    have kp : ProgKeep cfg.K.M base (jointWork cfg) s t := hk.mono (by decide +kernel)
    exact ⟨kp,hs.next JointLayout.layout kp hi hj (jointExternal_frame kp hsym hs.external)⟩
  peer := by
    intro A j s hj hA hs h19
    exact CachedField.digit_ok JointLayout.layout (by decide) hm hC ha hOne hj hQ hA
      jointExternal_frame hs h19
  generator := by
    intro A j s hj hA hs h19
    exact jointFixedDigit_ok Forward.Arithmetic.cases JointLayout.fixedLayout hm
      (by decide) hC ha hOne hP hA hs hj h19


theorem jointInitCounter_ok (s : State) :
    WP isa (.block [.movz .x .x19 256 0]) s fun t =>
      t.gpr .x19=256 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,RegUpd.gpr_write,
    Size.bits,show 16*0<64 by decide,ite_true,
    Option.some.injEq,exists_eq_left']
  exact ⟨rfl,⟨fun r hr => by
    have h : r≠.x19 := by simpa using hr
    simp only [RegUpd.gpr_write,h,ite_false],rfl,rfl,rfl,rfl⟩⟩

/-- Initialize the shared accumulator after both digit strings and tables are ready. -/
theorem jointInit_ok {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hOne : cfg.K.one<C.p) {s : State}
    (hi : Inv cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) (tmv C cfg.K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s) (hg : JointGenerator cfg C base 8192 P T s) :
    WP isa (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr))) s fun t =>
      JointLoopKeep cfg.K.M base (jointWork cfg) s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T) .infinity t ∧
      t.gpr .x19=256 := by
  rw [WP.block_append_iff]
  refine WP.mono_syms (infinityPoint_ok (K:=cfg.K) (o:=cfg.K.R)
    JointLayout.layout.lay JointLayout.layout.aligned (by decide +kernel) hi hOne)
    fun a ⟨E,ka,ia,ja⟩ sy => ?_
  have kp : ProgKeep cfg.K.M base (jointWork cfg) s a := ka.mono (by decide +kernel)
  have il := ia.sub (fun _ hx => List.mem_append_right _ hx)
  have st := hs.keep kp (fun r hr => by
    have := JointLayout.layout.stableBounds r hr
    have := hi.scr.nowrap
    omega) JointLayout.layout.stableSep
  have ca : JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T) .infinity a :=
    ⟨il.to_tmv,st,jointExternal_frame kp sy hg,il.point_tmv (jointLive_R cfg) ja⟩
  refine WP.mono_syms (jointInitCounter_ok a) fun t ⟨t19,kt⟩ sy' => ?_
  have ct := ca.of_keeps kt (by decide) (show JointGenerator cfg C base 8192 P T t from
    { symbol := by rw [sy']; exact ca.external.symbol
      read := by simpa only [kt.rd,kt.wr] using ca.external.read
      outside := ca.external.outside
      bounds := by simpa only [kt.mem] using ca.external.bounds
      point := by simpa only [kt.mem] using ca.external.point })
  exact ⟨⟨(JointLoopKeep.of_prog kp).regs.trans ((Keeps.regs kt).mono (by simp)),
    by simpa only [kt.mem] using kp.unch⟩,ct,t19⟩

/-- Both public scalar products are accumulated in the same Jacobian point. -/
theorem jointInitializedRun_ok {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hm : UnitMod C.p (2^(64*cfg.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : cfg.K.one<C.p) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) {s : State}
    (hi : Inv cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) (tmv C cfg.K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s) (hg : JointGenerator cfg C base 8192 P T s) :
    WP isa (.seq (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
      (Joint.run cfg P256Joint.ops)) s fun t =>
      JointLoopKeep cfg.K.M base (jointWork cfg) s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)
        (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  apply WP.seq
  refine WP.mono (jointInit_ok hOne hi hs hg) fun a ⟨ka,ca,a19⟩ => ?_
  refine WP.mono (jointRun_ok hC hP hQ (jointOps_ok hm hC ha hOne hP hQ) hu hv ca a19)
    fun t ⟨kt,ct,t19⟩ => ⟨ka.trans kt,ct,t19⟩

end VG.Proof.Ecdsa.Verify.AArch64
