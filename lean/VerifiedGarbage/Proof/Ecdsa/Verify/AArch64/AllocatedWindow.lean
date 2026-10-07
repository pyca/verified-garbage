import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedMixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointWindow

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
