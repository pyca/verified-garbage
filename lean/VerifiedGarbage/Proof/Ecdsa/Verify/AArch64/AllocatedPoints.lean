import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsFrame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

structure BodyPost (base : Addr) (P : Point C) (s t : State) : Prop where
  scr : Scr t base size
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  unch : Unch base bodyRanges s.mem t.mem
  bounds : ∀ i∈[RX,RY,RZ],sv p256 base t i<C.p
  point : Rep C (tmv C 4 base t (p256.sl RX)) (tmv C 4 base t (p256.sl RY))
    (tmv C 4 base t (p256.sl RZ)) P

theorem body_ok (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre p256 s₀ (s₀.syms p256.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V)) s
      (BodyPost base (add (mul (sv p256 base s U) (G C)) (mul (sv p256 base s V) P)) s) := by
  have hm := unitMod_pow_two hc.p_odd (64*p256.n)
  have hOne : K.one<C.p := by
    change 2^256%C.p<C.p
    exact Nat.mod_lt _ (by decide)
  have hone : toM C.p (2^(64*K.M.n)) K.one=1 := toM_cmont hc 1
  rw [Joint.points,Joint.window]
  apply WP.assoc
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (jointSetup_ok hc hC hT hM hTP hP hrep)) fun a ia => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (initializedRun_ok raw hC hc.am3 hm hOne hc.onG hP
    (show sv p256 base s U<2^256 from wordsVal_lt ..)
    (show sv p256 base s V<2^256 from wordsVal_lt ..) ia.field ia.stable ia.generator)
    fun b ⟨kb,ib,_⟩ => ?_)
  refine WP.mono (jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl) hm hC hOne hone
    (by decide) ib) fun t ⟨kt,ut,_,lt,rep⟩ => ?_
  have u1 : Unch base bodyRanges s.mem a.mem := ia.unch.mono (fun _ h => List.mem_append_left _ h)
  have u2 : Unch base bodyRanges a.mem b.mem := kb.unch.cover (by decide +kernel)
  have u3 : Unch base bodyRanges b.mem t.mem := ut.cover (by decide +kernel)
  have un := ((u1.trans u2).mono (fun _ h => (List.mem_append.mp h).elim id id)).trans u3
  refine ⟨ib.field.scr.of_keepRegs kt (by decide),kt.rd.trans (kb.regs.rd.trans ia.rd),
    kt.wr.trans (kb.regs.wr.trans ia.wr),kt.sp.trans (kb.regs.sp.trans ia.sp),
    un.mono (fun _ h => (List.mem_append.mp h).elim id id),?_,rep⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl|hi
  · exact lt _ (by decide)
  rcases List.mem_cons.mp hi with rfl|hi
  · exact lt _ (by decide)
  rcases List.mem_singleton.mp hi with rfl
  exact lt _ (by decide)

/-- Allocated point arithmetic restores its additional callee-saved registers and
returns the same numerical and geometric verification postcondition. -/
theorem points_ok (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre p256 s₀ (s₀.syms p256.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa P256Allocated.points s fun t => FinalState p256 s₀ base g t ∧
      Rep C (tmv C 4 base t (p256.sl RX)) (tmv C 4 base t (p256.sl RY))
        (tmv C 4 base t (p256.sl RZ))
        (add (mul (sv p256 base s U) (G C)) (mul (sv p256 base s V) P)) ∧
      ∀ r∈allocatedExtraRegs,t.gpr r=s.gpr r := by
  unfold P256Allocated.points
  apply WP.seq
  refine WP.mono_syms (allocatedSave_ok hM.scr (by decide)) fun a ⟨ka,ua,sa⟩ sya => ?_
  have ma := mid_saved hM ka ua sya
  have repa : Rep C (tmv C 4 base a (p256.sl PX)) (tmv C 4 base a (p256.sl PY))
      (tmv C 4 base a (p256.sl ONEP)) P := by
    change Rep C (toM _ _ (sv p256 base a PX)) (toM _ _ (sv p256 base a PY))
      (toM _ _ (sv p256 base a ONEP)) P
    rw [save_same ua PX (by decide),save_same ua PY (by decide),save_same ua ONEP (by decide)]
    exact hrep
  refine WP.seq (WP.mono (body_ok raw_correct hc hC hT ma hTP hP repa) fun b hb => ?_)
  have sb := allocatedSaved_keep sa hb.unch (by decide +kernel)
  refine WP.mono (allocatedRestore_ok hb.scr (by decide) sb) fun t ⟨kt,extra⟩ => ?_
  have whole : Unch base pointRanges s.mem t.mem := by
    rw [kt.mem]
    exact (ua.unch.trans hb.unch).mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw|hw
      · exact List.mem_append_right _ hw
      · exact List.mem_append_left _ hw)
  have bounds : ∀ i∈[RX,RY,RZ],sv p256 base t i<C.p := by simpa only [sv,kt.mem] using hb.bounds
  refine ⟨finalState_of_allocated hM (hb.scr.of_keepRegs (show KeepRegs allocatedExtraRegs b t from ⟨kt.gpr,kt.rd,kt.wr,kt.sp⟩) (by decide))
    (kt.rd.trans (hb.rd.trans ka.rd)) (kt.wr.trans (hb.wr.trans ka.wr)) whole
    (bounds _ (by decide)) (bounds _ (by decide)),?_,extra⟩
  have rep := hb.point
  rw [save_same ua U (by decide),save_same ua V (by decide)] at rep
  simpa only [tmv,kt.mem] using rep

/-- The extra-register wrapper preserves precisely the verifier's untouched registers. -/
theorem points_untouched (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre p256 s₀)
    (hm : Mid p256 s₀ (s₀.gpr .x3) g s) :
    WP isa P256Allocated.points s fun t => ∀ r∈untouched,t.gpr r=s.gpr r := by
  let P := peerPt p256 (s₀.mem (s₀.gpr .x0)=4) (keyX p256 s₀) (keyY p256 s₀)
  have hP : onCurve p256.C P=true := peerPt_onCurve hc _ _ _
  have hr : Rep p256.C (tmv p256.C 4 (s₀.gpr .x3) s (p256.sl PX))
      (tmv p256.C 4 (s₀.gpr .x3) s (p256.sl PY))
      (tmv p256.C 4 (s₀.gpr .x3) s (p256.sl ONEP)) P := by
    have hOne : tmv p256.C 4 (s₀.gpr .x3) s (p256.sl ONEP)=1 := onep_tmv hc hm.fixed
    rw [hOne]
    exact peerPt_rep hC _ _ _ hm.px hm.py
  exact WP.mono (points_ok hc hC hT hm hp.tbl hP hr) fun _ h => h.2.2

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
