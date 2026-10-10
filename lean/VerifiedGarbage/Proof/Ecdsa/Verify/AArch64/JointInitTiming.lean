import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Inplace
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedMixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCacheTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming

/-! ## `JointWindow` -/

section

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

end

/-! ## `AllocatedWindow` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 Spec.Weierstrass

/-- A read-only generator outside scratch survives the allocator's spills. -/
def ExternalFrame (base : Addr) (External : State → Prop) : Prop :=
  ∀ {s t},Frame base work s t → t.syms=s.syms → External s → External t

theorem external_frame {base T : Addr} {P : Point C} :
    ExternalFrame base (JointGenerator cfg C base 8192 P T) :=
  fun hk hsym hs => hs.allocatedKeep hk hsym work_bounds

theorem cachedSum_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base : Addr} {u v : Nat} {Q A B : Point C} {External : State → Prop}
    (hExt : ExternalFrame base External) (hA : onCurve C A=true) (hB : onCurve C B=true) {s : State}
    (h : JointCore cfg C base 8192 Q u v External A s)
    (hi : Inv K.M base 8192 C.p Sl (CachedField.entryLive (jointLive cfg)) (tmv C K.M.n base s) s)
    (hj : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B)
    (h2 : tmv C K.M.n base s 5400=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z)
    (h3 : tmv C K.M.n base s 5432=tmv C K.M.n base s K.E.z*(tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z)) :
    WP isa (.seq (CachedJac.add K P256Allocated.cachedOps) (.block (copyPt 4 K.R K.D))) s fun t =>
      Frame base work s t ∧ JointCore cfg C base 8192 Q u v External (add A B) t := by
  apply WP.of_syms
  apply WP.seq
  refine WP.mono (cachedAdd_ok raw hC ha hm hOne hi (by decide +kernel) h2 h3 hA hB h.point hj)
    fun b ⟨eb,kb,ib,jb⟩ => ?_
  refine WP.mono (copyPoint_ok JointLayout.layout.lay JointLayout.layout.aligned
    JointLayout.fixedLayout.copyApart (by decide +kernel) ib (by decide +kernel))
    fun t ⟨et,kt,it,hv⟩ sy => ?_
  have kp := kb.trans (liftProg kt (by decide +kernel))
  refine ⟨kp,h.allocatedNext JointLayout.layout kp work_stable
    (it.sub (fun x hx => by simp [CachedField.entryLive,hx])) ?_ (hExt kp sy h.external)⟩
  simp only [Prod.mk.injEq] at hv
  change et 512=eb 608 ∧ et 544=eb 640 ∧ et 576=eb 672 at hv
  change InvJ C (et 512) (et 544) (et 576) (add A B)
  rw [hv.1,hv.2.1,hv.2.2]
  exact jb

theorem mixedSum_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base : Addr} {u v : Nat} {Q A B : Point C} {External : State → Prop}
    (hExt : ExternalFrame base External) (hA : onCurve C A=true) (hB : onCurve C B=true) {s : State}
    (h : JointCore cfg C base 8192 Q u v External A s)
    (hi : Inv K.M base 8192 C.p Sl ([K.E.x,K.E.y,K.E.z]++jointLive cfg) (tmv C K.M.n base s) s)
    (hj : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B)
    (hz : tmv C K.M.n base s K.E.z=1) :
    WP isa (.seq P256Allocated.mixedAdd (.block (copyPt 4 K.R K.D))) s fun t =>
      Frame base work s t ∧ JointCore cfg C base 8192 Q u v External (add A B) t := by
  apply WP.of_syms
  apply WP.seq
  refine WP.mono (mixedAdd_ok raw hC ha hm hOne hi (by decide +kernel) hA hB h.point hj hz)
    fun b ⟨eb,kb,ib,jb⟩ => ?_
  refine WP.mono (copyPoint_ok JointLayout.layout.lay JointLayout.layout.aligned
    JointLayout.fixedLayout.copyApart (by decide +kernel) ib (by decide +kernel))
    fun t ⟨et,kt,it,hv⟩ sy => ?_
  have kp := kb.trans (liftProg kt (by decide +kernel))
  refine ⟨kp,h.allocatedNext JointLayout.layout kp work_stable
    (it.sub (fun x hx => by simp [hx])) ?_ (hExt kp sy h.external)⟩
  simp only [Prod.mk.injEq] at hv
  change et 512=eb 608 ∧ et 544=eb 640 ∧ et 576=eb 672 at hv
  change InvJ C (et 512) (et 544) (et 576) (add A B)
  rw [hv.1,hv.2.1,hv.2.2]
  exact jb

theorem ops_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base T : Addr} {P Q : Point C} {u v : Nat} (hP : onCurve C P=true) (hQ : onCurve C Q=true) :
    AllocatedJointOpsOk cfg P256Allocated.ops C base allocatedRegs work
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) P Q u v where
  counter := allocatedRegs_x19
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
    refine WP.mono_syms (double_ok raw hC ha hs.field hA hs.point) fun t ⟨hk,hi,hj⟩ hsym => ?_
    exact ⟨hk,hs.allocatedNext JointLayout.layout hk work_stable hi hj
      (external_frame hk hsym hs.external)⟩
  peer := by
    intro A j s hj hA hs h19
    exact CachedField.allocatedCachedDigit_ok JointLayout.layout (by decide) hm hC
      clob4_allocatedRegs work_cover hj hQ hA jointExternal_frame
      (by intro A B s hA hB hs hi hj h2 h3
          exact cachedSum_ok raw hC ha hm hOne external_frame hA hB hs hi hj h2 h3) hs h19
  generator := by
    intro A j s hj hA hs h19
    exact allocatedJointFixedDigit_ok JointLayout.fixedLayout hm hC clob4_allocatedRegs work_cover hP hA
      (by intro A B s hA hB hs hi hj hz
          exact mixedSum_ok raw hC ha hm hOne external_frame hA hB hs hi hj hz) hs hj h19

theorem initializedRun_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base T : Addr} {P Q : Point C} {u v : Nat} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) {s : State}
    (hi : Inv K.M base 8192 C.p Sl (jointLive cfg) (tmv C K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s) (hg : JointGenerator cfg C base 8192 P T s) :
    WP isa (.seq (.block (Jacobian.infinity K K.R++([.movz .x .x19 256 0] : List Instr)))
      (Joint.run cfg P256Allocated.ops)) s fun t =>
      AllocatedFrame (.x19::allocatedRegs) base work s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)
        (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  apply WP.seq
  refine WP.mono (jointInit_ok hOne hi hs hg) fun a ⟨ka,ca,a19⟩ => ?_
  have k' : AllocatedFrame (.x19::allocatedRegs) base work s a :=
    ⟨ka.regs.mono (fun r hr => (List.mem_cons.mp hr).elim (fun h => List.mem_cons.mpr (Or.inl h))
      (fun h => List.mem_cons_of_mem _ (clob4_allocatedRegs r h))),ka.unch.cover work_cover⟩
  refine WP.mono (allocatedJointRun_ok hC hP hQ (ops_ok raw hC ha hm hOne hP hQ) hu hv ca a19)
    fun t ⟨kt,ct,t19⟩ => ⟨k'.trans kt,ct,t19⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `JointInitTiming` -/

section

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

end
