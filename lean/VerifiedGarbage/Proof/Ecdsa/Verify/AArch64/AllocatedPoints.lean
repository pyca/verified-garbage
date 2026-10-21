module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGenerator
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyExtra
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.P256.VerifyTable.Build
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
import VerifiedGarbage.Proof.P256.VerifyTable.Env
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Allocated P-256 verification points

The register-allocated verification builds `Q`'s odd multiples by co-Z
arithmetic (`Impl/P256/VerifyTable.lean`), which leaves their cached powers
of `Z` too, then runs the joint loop. -/

@[expose] public section

/-! ## `AllocatedSetup` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

/-- What the co-Z table writes: what the joint table and cache write, and the
working space of ECDH's allocated blocks. -/
def allocatedSetupRanges : List (Nat×Nat) := jointPointRanges++[(7104,576)]

theorem buildW_cover : ∀ w∈Proof.P256.VerifyTable.buildW,∃ r∈allocatedSetupRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem tablePt_dst (a : Nat) :
    (Jacobian.tablePt P256Joint.cfg.K a).x=Proof.P256.VerifyTable.dst a 0 ∧
    (Jacobian.tablePt P256Joint.cfg.K a).y=Proof.P256.VerifyTable.dst a 1 ∧
    (Jacobian.tablePt P256Joint.cfg.K a).z=Proof.P256.VerifyTable.dst a 2 :=
  ⟨rfl,rfl,rfl⟩

theorem tableZ_dst (i : Nat) :
    CachedJac.tableZ2 i=Proof.P256.VerifyTable.dst (i+1) 3 ∧
    CachedJac.tableZ3 i=Proof.P256.VerifyTable.dst (i+1) 4 := by
  simp only [CachedJac.tableZ2,CachedJac.tableZ3,Proof.P256.VerifyTable.dst,Nat.reduceLT,↓reduceIte,
    Nat.add_sub_cancel,Nat.reduceSub]
  omega

theorem build_slots : ∀ x∈Proof.P256.VerifyTable.buildSlots,x∈jointSlots P256Joint.cfg := by
  decide +kernel

theorem build_live : ∀ x∈jointLive P256Joint.cfg,
    x∈Proof.P256.VerifyTable.copiesV Proof.P256.VerifyTable.l4 (Proof.P256.VerifyTable.Vl 7) := by
  decide +kernel

theorem build_entries : ∀ a<8,∀ j<5,Proof.P256.VerifyTable.dst (a+1) j∈
    Proof.P256.VerifyTable.copiesV Proof.P256.VerifyTable.l4 (Proof.P256.VerifyTable.Vl 7) := by
  decide +kernel

/-- The co-Z table from the prepared state: the odd multiples of `Q` with
their cached powers, everything else the joint loop reads unchanged. -/
theorem buildStage_ok (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    {base : Addr} {g : Reg → BitVec 64} {P : Point p256.C} (hP : onCurve p256.C P=true)
    {s₀ s : State} (h : JointPrepPost base g P s₀ s) :
    WP isa Impl.P256.VerifyTable.build s fun t =>
      AllocatedFrame Proof.P256.VerifyTable.regs base Proof.P256.VerifyTable.buildW s t ∧
      Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
        (jointLive P256Joint.cfg) (tmv p256.C 4 base t) t ∧
      JointStable P256Joint.cfg p256.C base P (sv p256 base s₀ U) (sv p256 base s₀ V) t := by
  have hi : Inv Proof.P256.VerifyTable.M base 8192 Proof.P256.VerifyTable.C.p
      (·∈jointSlots P256Joint.cfg) Proof.P256.VerifyTable.V0 (tmv p256.C 4 base s) s :=
    h.field.mono_sl fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
  refine WP.mono (Proof.P256.VerifyTable.build_field JointLayout.layout.lay JointLayout.layout.aligned
    build_slots hi) fun t ⟨kt,it⟩ => ?_
  have un := kt.unch
  have val (x : Nat) (hx : x∈Proof.P256.VerifyTable.copiesV Proof.P256.VerifyTable.l4
      (Proof.P256.VerifyTable.Vl 7)) :
      tmv p256.C 4 base t x=Proof.P256.VerifyTable.buildEnv (tmv p256.C 4 base s) x := it.val x hx
  have h1 : tmv p256.C 4 base s 224=1 := h.one
  have jp : InvJ p256.C (tmv p256.C 4 base s 1280) (tmv p256.C 4 base s 1440) 1 P := by
    have := h.peer.2.2
    change InvJ p256.C (tmv p256.C 4 base s 1280) (tmv p256.C 4 base s 1440)
      (tmv p256.C 4 base s 224) P at this
    rw [h1] at this
    exact this
  have env := Proof.P256.VerifyTable.build_env hC hc.am3 hO hP jp h1
  have ev (a : Nat) (ha : 1≤a) (ha8 : a≤8) (j : Nat) (hj : j<5) :
      tmv p256.C 4 base t (Proof.P256.VerifyTable.dst a j)=
        Proof.P256.VerifyTable.buildEnv (tmv p256.C 4 base s) (Proof.P256.VerifyTable.dst a j) := by
    apply val
    have := build_entries (a-1) (by omega) j hj
    rwa [show a-1+1=a by omega] at this
  have keep (x : Nat) (hx : ∀ w∈Proof.P256.VerifyTable.buildW,x+8*4≤w.1 ∨ w.1+w.2≤x)
      (hb : x+8*4≤2^64) : wordsVal t.mem base x 4=wordsVal s.mem base x 4 := un.wordsVal hx hb
  refine ⟨kt,(it.sub build_live).to_tmv,⟨⟨?_,fun a ha h8 => ?_,fun j hj => ?_⟩,fun j hj => ?_,?_,
    fun i hi => ?_,fun i hi => ?_⟩⟩
  · rw [show P256Joint.cfg.K.M.n=4 from rfl,keep _ (by decide) (by decide)]; exact h.peer.1
  · obtain ⟨ex,ey,ez⟩ := tablePt_dst a
    rw [show P256Joint.cfg.K.M.n=4 from rfl,ex,ey,ez,ev a ha h8 0 (by decide),ev a ha h8 1 (by decide),ev a ha h8 2 (by decide)]
    exact (env a ha h8).1
  · rw [un.byte (fun w hw => ?_) (by change 1824+j<2^64; omega)]
    · exact h.peer.2.1 j hj
    · have : ∀ w∈Proof.P256.VerifyTable.buildW,2088≤w.1 ∨ w.1+w.2≤1824 := by decide
      have := this w hw
      change 1824+j+1≤w.1 ∨ w.1+w.2≤1824+j
      omega
  · change j<514 at hj
    rw [un.byte (fun w hw => ?_) (by change 2112+j<2^64; omega)]
    · exact h.generator j hj
    · have : ∀ w∈Proof.P256.VerifyTable.buildW,2632≤w.1 ∨ w.1+w.2≤2112 := by decide
      have := this w hw
      change 2112+j+1≤w.1 ∨ w.1+w.2≤2112+j
      omega
  · change toM _ _ (wordsVal t.mem base P256Joint.cfg.onep 4)=1
    rw [keep _ (by decide) (by decide)]
    exact h.one
  · obtain ⟨e2,_⟩ := tableZ_dst i
    obtain ⟨_,_,ez⟩ := tablePt_dst (i+1)
    rw [show P256Joint.cfg.K.M.n=4 from rfl,e2,ez,ev (i+1) (by omega) (by omega) 3 (by decide),ev (i+1) (by omega) (by omega) 2 (by decide)]
    exact (env (i+1) (by omega) (by omega)).2.1
  · obtain ⟨e2,e3⟩ := tableZ_dst i
    obtain ⟨_,_,ez⟩ := tablePt_dst (i+1)
    rw [show P256Joint.cfg.K.M.n=4 from rfl,e3,e2,ez,ev (i+1) (by omega) (by omega) 4 (by decide),ev (i+1) (by omega) (by omega) 3 (by decide),
      ev (i+1) (by omega) (by omega) 2 (by decide)]
    exact (env (i+1) (by omega) (by omega)).2.2

def allocatedSetup : Prog isa := .seq jointPrepProgram <|
  .seq Impl.P256.VerifyTable.build (.block [])

structure AllocatedSetupPost (base T : Addr) (P : Point p256.C) (u v : Nat) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (jointLive P256Joint.cfg) (tmv p256.C 4 base t) t
  stable : JointStable P256Joint.cfg p256.C base P u v t
  generator : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size (G p256.C) T t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  unch : Unch base allocatedSetupRanges s.mem t.mem
  syms : t.syms=s.syms

theorem allocatedSetup_bounds : ∀ w∈allocatedSetupRanges,w.1+w.2≤size := by decide +kernel

theorem allocatedSetup_ok (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre P256Joint.p256v s₀ (s₀.syms P256Joint.p256v.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa allocatedSetup s
      (AllocatedSetupPost base (s₀.syms P256Joint.p256v.tsym) P (sv p256 base s U) (sv p256 base s V) s) := by
  unfold allocatedSetup
  refine WP.seq (WP.mono (jointPrepStage_ok hc hC hM.scr hM.fixed hM.px_lt hM.py_lt hrep)
    fun a ia => ?_)
  refine WP.seq (WP.mono_syms (buildStage_ok hc hC hO hP ia) fun b ⟨kb,ib,sb⟩ sy => ?_)
  apply WP.of_runBlock
  refine ⟨b,rfl,?_⟩
  have u1 : Unch base allocatedSetupRanges s.mem a.mem :=
    (ia.unch.cover jointPoint_prep).mono fun _ h => List.mem_append_left _ h
  have u2 : Unch base allocatedSetupRanges a.mem b.mem := kb.unch.cover buildW_cover
  have un : Unch base allocatedSetupRanges s.mem b.mem :=
    (u1.trans u2).mono fun _ hw => (List.mem_append.mp hw).elim id id
  have rd : b.rd=s.rd := kb.regs.rd.trans ia.keep.rd
  have wr : b.wr=s.wr := kb.regs.wr.trans ia.keep.wr
  have ss : b.syms=s.syms := sy.trans ia.syms
  have whole : Unch base [(0,size)] s₀.mem b.mem := unch_whole (hM.unch.trans un) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · exact allocatedSetup_bounds w hw)
  obtain ⟨table,outside⟩ := tbl_of hTP (rd.trans hM.rd) whole
  have gen := JointGenerator.of_table hc hC hT table outside (by rw [ss,hM.syms]; rfl)
  exact ⟨ib,sb,gen,rd,wr,kb.regs.sp.trans ia.keep.sp,un,ss⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedPointsFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

def bodyRanges : List (Nat × Nat) := jointPointRanges++[(7104,576)]
def pointRanges : List (Nat × Nat) := bodyRanges++[(7800,32)]

theorem point_bounds : ∀ w∈pointRanges,w.1+w.2≤size := by decide +kernel
theorem point_fixed : FixedOk p256 pointRanges := by unfold FixedOk; decide +kernel

theorem save_same {s t : State} {base : Addr}
    (hu : Outside base 7800 32 s.mem t.mem) :
    ∀ i<45,sv p256 base t i=sv p256 base s i := by
  intro i hi
  apply hu.unch.wordsVal
  · have h : ∀ i<45,∀ w∈[(7800,32)],p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
    exact h i hi
  · have h : ∀ i<45,p256.sl i+32≤2^64 := by decide +kernel
    exact h i hi

/-- Saving extra registers touches no scalar, flag, peer or fixed verifier data. -/
theorem mid_saved {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hk : KeepRegs [] s t)
    (hu : Outside base 7800 32 s.mem t.mem) (hsy : t.syms=s.syms) :
    Mid p256 s₀ base g t := by
  have same := save_same hu
  have whole : Unch base [(0,size)] s₀.mem t.mem := unch_whole (h.unch.trans hu.unch) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · rw [List.mem_singleton.mp hw]; decide)
  refine ⟨h.scr.of_keepRegs hk (by simp),hk.wr.trans h.wr,hk.rd.trans h.rd,
    h.fixed.unch (by decide) h.scr.nowrap (by unfold FixedOk; decide +kernel) hu.unch,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,whole,hsy.trans h.syms,?_⟩
  · rw [same RX (by decide)]; exact h.rx
  · rw [same RY (by decide)]; exact h.ry
  · rw [same RZ (by decide)]; exact h.rz
  · rw [hu.unch.word (by decide +kernel) (by decide)]; exact h.flag
  · rw [same PX (by decide)]; exact h.px_lt
  · rw [same PY (by decide)]; exact h.py_lt
  · rw [same PX (by decide)]; exact h.px
  · rw [same PY (by decide)]; exact h.py
  · rw [same RM' (by decide)]; exact h.rm_lt
  · rw [same RM' (by decide)]; exact h.rm
  · rw [same U (by decide)]; exact h.u_lt
  · rw [same U (by decide)]; exact h.u
  · rw [same V (by decide)]; exact h.v_lt
  · rw [same V (by decide)]; exact h.v
  · rw [same VG.Impl.Ecdsa.AArch64.K (by decide)]; exact h.k

/-- The allocated body preserves the numerical inputs to the final check. -/
theorem finalState_of_allocated {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hs : Scr t base size)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hu : Unch base pointRanges s.mem t.mem)
    (hx : sv p256 base t RX<p256.C.p) (hz : sv p256 base t RZ<p256.C.p) :
    FinalState p256 s₀ base g t := by
  have same (i : Nat) (hi : i∈[RM',VG.Impl.Ecdsa.AArch64.K]) : sv p256 base t i=sv p256 base s i := by
    apply hu.wordsVal
    · have he : ∀ i∈[RM',VG.Impl.Ecdsa.AArch64.K],∀ w∈pointRanges,p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
      exact he i hi
    · have he : ∀ i∈[RM',VG.Impl.Ecdsa.AArch64.K],p256.sl i+32≤2^64 := by decide +kernel
      exact he i hi
  refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap point_fixed hu,
    ?_,?_,?_,hz,?_,?_,hx⟩
  · rw [hu.word (by decide +kernel) (by decide)]; exact h.flag
  · rw [same RM' (by simp)]; exact h.rm_lt
  · change toM _ _ (sv p256 base t RM')=_
    rw [same RM' (by simp)]; exact h.rm
  · exact unch_whole (h.unch.trans hu) (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
      · exact point_bounds w hw)
  · rw [same VG.Impl.Ecdsa.AArch64.K (by simp)]; exact h.k

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `AllocatedPoints` -/

section

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

theorem body_ok (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre P256Joint.p256v s₀ (s₀.syms P256Joint.p256v.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V)) s
      (BodyPost base (add (mul (sv p256 base s U) (G C)) (mul (sv p256 base s V) P)) s) := by
  have hm := unitMod_pow_two hc.p_odd (64*p256.n)
  have hOne : K.one<C.p := by
    change 2^256%C.p<C.p
    exact Nat.mod_lt _ (by decide)
  have hone : toM C.p (2^(64*K.M.n)) K.one=1 := toM_cmont hc.toBaseCfgOk 1
  rw [Joint.points,Joint.window]
  apply WP.assoc
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (allocatedSetup_ok hc hC hO hT hM hTP hP hrep)) fun a ia => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (initializedRun_ok raw hC hc.am3 hm hOne hc.onG hP
    (show sv p256 base s U<2^256 from wordsVal_lt ..)
    (show sv p256 base s V<2^256 from wordsVal_lt ..) ia.field ia.stable ia.generator)
    fun b ⟨kb,ib,_⟩ => ?_)
  refine WP.mono (jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl) hm hC hOne hone
    (by decide) ib) fun t ⟨kt,ut,_,lt,rep⟩ => ?_
  have u1 : Unch base bodyRanges s.mem a.mem := ia.unch
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
theorem points_ok (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre P256Joint.p256v s₀ (s₀.syms P256Joint.p256v.tsym) base)
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
  refine WP.seq (WP.mono (body_ok raw_correct hc hC hO hT ma hTP hP repa) fun b hb => ?_)
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
theorem points_untouched (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
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
  exact WP.mono (points_ok hc hC hO hT hm hp.tbl hP hr) fun _ h r hr => h.2.2 r (by revert hr; revert r; decide)

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end
