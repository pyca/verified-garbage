module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! ## `JointPrep` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

def jointPrepRanges : List (Nat×Nat) := [(P256Joint.cfg.gBits,264),(P256Joint.cfg.K.bits,264)]

def jointPrepProgram : Prog isa :=
  .seq (Impl.Weierstrass.AArch64.FastNaf.prep P256Joint.cfg.G (p256.sl U) 7)
    (Impl.Weierstrass.AArch64.FastNaf.prep P256Joint.cfg.K (p256.sl V) 5)

structure JointPrepPost (base : Addr) (g : Reg → BitVec 64) (P : Point p256.C) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jacWinSlots P256Joint.cfg.K)
    (winRo P256Joint.cfg.K) (tmv p256.C 4 base t) t
  peer : NafWindowInput P256Joint.cfg.K p256.C base P (sv p256 base s V) t
  generator : ∀ i<257,t.mem (off base (P256Joint.cfg.gBits+i))=FastNaf.byte 7 (sv p256 base s U) i
  fixed : Fixed p256 base g t.mem
  one : tmv p256.C 4 base t P256Joint.cfg.onep=1
  same : ∀ i<45,sv p256 base t i=sv p256 base s i
  keep : KeepRegs nafPrepClob s t
  unch : Unch base jointPrepRanges s.mem t.mem
  syms : t.syms=s.syms

theorem apart_jointPrep {i : Nat} (hi : i<45) :
    ∀ w∈jointPrepRanges,p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i := by
  intro w hw
  simp only [jointPrepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · apply Or.inl; rw [sl_eq4 p256 (by decide)]; change 64+32*i+32≤1504; omega
  · apply Or.inl; rw [sl_eq4 p256 (by decide)]; change 64+32*i+32≤1824; omega

theorem jointPrepStage_ok (hc : CfgOk p256) (hC : Law p256.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed p256 base g s.mem) {P : Point p256.C}
    (hpx : sv p256 base s PX<p256.C.p) (hpy : sv p256 base s PY<p256.C.p)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa jointPrepProgram s (JointPrepPost base g P s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x,p256.mont x<p256.C.p := fun x => Nat.mod_lt _ (by omega)
  refine WP.mono_syms (Weierstrass.AArch64.jointPrep_ok P256Joint.cfg hs
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inl JointLayout.bits_disjoint) (by decide)) fun s₂ ⟨hs₂,bG,bQ,k₂,U₂⟩ sy₂ => ?_
  have F₂ := F.unch h7 hn (W:=jointPrepRanges) (by unfold FixedOk jointPrepRanges; decide) U₂
  have e₂ : ∀ {i},i<45 → sv p256 base s₂ i=sv p256 base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_jointPrep hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv p256.C p256.n base s₂ (p256.sl i) = tmv p256.C p256.n base s (p256.sl i) := fun hi => by
    show toM _ _ (sv p256 base s₂ _) = toM _ _ (sv p256 base s _); rw [e₂ hi]
  have hlt : ∀ x∈winRo (P256Joint.cfg.K),wordsVal s₂.mem base x p256.n<p256.C.p := by
    intro x hx
    simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega)
    · exact lt_of_eq_of_lt (e₂ (i:=PX) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i:=PY) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
  have hI : Inv (P256Joint.cfg.K).M base size p256.C.p (·∈jacWinSlots (P256Joint.cfg.K))
      (winRo (P256Joint.cfg.K)) (tmv p256.C p256.n base s₂) s₂ :=
    ⟨hs₂,hM₂,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),hlt,fun _ _ => rfl⟩
  have one : tmv p256.C p256.n base s₂ (p256.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (p256.sl ONEP) p256.n)=1
    rw [F₂.onep]
    have hm1 := toM_cmont hc.toBaseCfgOk 1
    have ho : Fin.ofNat p256.C.p 1 = (1:Fe p256.C) := by rfl
    simpa only [Cfg.mont,Cfg.R,Nat.one_mul,ho] using hm1
  have hp : Rep p256.C (tmv p256.C p256.n base s₂ (p256.sl PX)) (tmv p256.C p256.n base s₂ (p256.sl PY))
      (tmv p256.C p256.n base s₂ (p256.sl ONEP)) P := by
    rw [tv (by decide),tv (by decide),tv (by decide)]; exact hrep
  have hj : InvJ p256.C (tmv p256.C p256.n base s₂ (p256.sl PX)) (tmv p256.C p256.n base s₂ (p256.sl PY))
      (tmv p256.C p256.n base s₂ (p256.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one,Lean.Grind.Semiring.mul_one] using hh
  exact ⟨hI,⟨F₂.zero,fun i hi => bQ i hi,hj⟩,bG,F₂,one,fun _ hi => e₂ hi,k₂,U₂,sy₂⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

/-- The points stage writes only arithmetic work, public digits, and precomputation. -/
def jointPointRanges : List (Nat×Nat) :=
  [(128,32),(512,544),(1504,584),(2848,1536),(5400,64),(6000,512)]

theorem jointPoint_fixed : FixedOk p256 jointPointRanges := by unfold FixedOk; decide +kernel

theorem jointPoint_bounds : ∀ w∈jointPointRanges,w.1+w.2≤size := by decide +kernel

theorem jointPoint_prep : ∀ w∈jointPrepRanges,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_table : ∀ w∈jacTreeWrites P256Joint.cfg.K,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_cache : ∀ w∈CachedInit.outputs.map (·,32)++[(128,32)],∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_loop : ∀ w∈(jointWork P256Joint.cfg).map (·,32)++[(128,32)],∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_finish : ∀ w∈jacLoopWrites P256Joint.cfg.K,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem jointPoint_union {base : Addr} {a b c : Mem}
    (h : Unch base jointPointRanges a b) (h' : Unch base jointPointRanges b c) :
    Unch base jointPointRanges a c :=
  (h.trans h').mono fun _ hw => (List.mem_append.mp hw).elim id id

/-- The point calculation preserves every scalar and flag needed by the final check. -/
theorem finalState_of_joint {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hs : Scr t base size)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr)
    (hu : Unch base jointPointRanges s.mem t.mem)
    (hx : sv p256 base t RX<p256.C.p) (hz : sv p256 base t RZ<p256.C.p) :
    FinalState p256 s₀ base g t := by
  have same (i : Nat) (hi : i∈[RM',K]) : sv p256 base t i=sv p256 base s i := by
    apply hu.wordsVal
    · have he : ∀ i∈[RM',K],∀ w∈jointPointRanges,p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
      exact he i hi
    · have he : ∀ i∈[RM',K],p256.sl i+32≤2^64 := by decide +kernel
      exact he i hi
  refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap jointPoint_fixed hu,
    ?_,?_,?_,hz,?_,?_,hx⟩
  · rw [hu.word (by decide +kernel) (by decide)]
    exact h.flag
  · rw [same RM' (by simp)]; exact h.rm_lt
  · change toM _ _ (sv p256 base t RM')=_
    rw [same RM' (by simp)]; exact h.rm
  · exact unch_whole (h.unch.trans hu) (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
      · exact jointPoint_bounds w hw)
  · rw [same K (by simp)]; exact h.k

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointTable` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

structure JointTablePost (base : Addr) (g : Reg → BitVec 64) (P : Point p256.C) (u v : Nat)
    (s t : State) : Prop where
  table : NafTableInv P256Joint.cfg.K p256.C base size P s t 8
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (nafLive P256Joint.cfg.K) (tmv p256.C 4 base t) t
  stable : NafStable P256Joint.cfg.K p256.C base P (FastNaf.byte 5 v) t
  generator : ∀ j<257,t.mem (off base (P256Joint.cfg.gBits+j))=FastNaf.byte 7 u j
  one : tmv p256.C 4 base t P256Joint.cfg.onep=1
  fixed : Fixed p256 base g t.mem
  syms : t.syms=s.syms

theorem jointTableStage_ok (certs : Forward.Arithmetic.Cases) (hc : CfgOk p256) (hC : Law p256.C)
    {base : Addr} {g : Reg → BitVec 64} {P : Point p256.C} (hP : onCurve p256.C P=true)
    {s₀ s : State} (h : JointPrepPost base g P s₀ s) :
    WP isa (ArithmeticTable.table P256Joint.cfg.K) s
      (JointTablePost base g P (sv p256 base s₀ U) (sv p256 base s₀ V) s) := by
  have hL := jacLay hc rfl
  refine WP.mono_syms (arithmeticTable_ok certs hL rfl (jacAligned p256 rfl)
    (unitMod_pow_two hc.p_odd _) (by decide) hC hc.am3 (by decide) (by change 2^(64*4)%p256.C.p<p256.C.p; exact Nat.mod_lt _ (by have := hc.p_ge; omega))
    hP h.field h.peer.2.2) fun t ht sy => ?_
  obtain ⟨hi,hstable⟩ := ht.ready hL h.peer.1 h.peer.2.1
  have F := h.fixed.unch hc.n10 h.field.scr.nowrap (W:=jacTreeWrites P256Joint.cfg.K)
    (by unfold FixedOk; decide +kernel) ht.unch
  have hone : tmv p256.C 4 base t P256Joint.cfg.onep=1 := by
    change toM _ _ (wordsVal t.mem base P256Joint.cfg.onep 4)=1
    have he := jacTree_ro_words hL ht.unch ht.field.scr.nowrap (x:=P256Joint.cfg.onep) (by decide +kernel)
    change wordsVal t.mem base P256Joint.cfg.onep 4=wordsVal s.mem base P256Joint.cfg.onep 4 at he
    rw [he]
    exact h.one
  refine ⟨ht,⟨hi.scr,hi.mod,?_,hi.lt,hi.val⟩,hstable,?_,hone,F,sy⟩
  · intro x hx
    exact List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx))
  · intro j hj
    rw [ht.unch.byte (fun w hw => ?_) (by change 1504+j<2^64; omega),h.generator j hj]
    have ha : ∀ w∈jacTreeWrites P256Joint.cfg.K,
        1768≤w.1 ∨ w.1+w.2≤1504 := by decide +kernel
    have hw' := ha w hw
    change 1504+j<w.1 ∨ w.1+w.2≤1504+j
    omega

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointSetup` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

def jointSetup : Prog isa := .seq jointPrepProgram <|
  .seq (ArithmeticTable.table P256Joint.cfg.K) (CachedJac.cache P256Joint.cfg.K)

structure JointSetupPost (base T : Addr) (P : Point p256.C) (u v : Nat) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (jointLive P256Joint.cfg) (tmv p256.C 4 base t) t
  stable : JointStable P256Joint.cfg p256.C base P u v t
  generator : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size (G p256.C) T t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  unch : Unch base jointPointRanges s.mem t.mem
  syms : t.syms=s.syms

theorem jointSetup_ok (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre p256 s₀ (s₀.syms p256.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa jointSetup s (JointSetupPost base (s₀.syms p256.tsym) P (sv p256 base s U) (sv p256 base s V) s) := by
  unfold jointSetup
  refine WP.seq (WP.mono (jointPrepStage_ok hc hC hM.scr hM.fixed hM.px_lt hM.py_lt hrep)
    fun a ia => ?_)
  refine WP.seq (WP.mono (jointTableStage_ok Forward.Arithmetic.cases hc hC hP ia) fun b ib => ?_)
  refine WP.mono_syms (jointCache_ok JointLayout.layout (unitMod_pow_two hc.p_odd _)
    ib.field ib.stable ib.generator ib.one) fun t ⟨kt,it,st⟩ sy => ?_
  have u1 := ia.unch.cover jointPoint_prep
  have u2 := ib.table.unch.cover jointPoint_table
  have u3 : Unch base jointPointRanges b.mem t.mem := kt.unch.cover jointPoint_cache
  have un := jointPoint_union (jointPoint_union u1 u2) u3
  have rd : t.rd=s.rd := kt.rd.trans (ib.table.keep.rd.trans ia.keep.rd)
  have wr : t.wr=s.wr := kt.wr.trans (ib.table.keep.wr.trans ia.keep.wr)
  have ss : t.syms=s.syms := sy.trans (ib.syms.trans ia.syms)
  have whole : Unch base [(0,size)] s₀.mem t.mem := unch_whole (hM.unch.trans un) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · exact jointPoint_bounds w hw)
  obtain ⟨table,outside⟩ := tbl_of hTP (rd.trans hM.rd) whole
  have gen := JointGenerator.of_table hc hC hT table outside (by rw [ss,hM.syms]; rfl)
  exact ⟨it,st,gen,rd,wr,kt.sp.trans (ib.table.keep.sp.trans ia.keep.sp),un,ss⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointPoints` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

/-- The interleaved multiplication returns the sum required by ECDSA verification. -/
theorem jointPoints_ok (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre p256 s₀ (s₀.syms p256.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa P256Joint.points s fun t => FinalState p256 s₀ base g t ∧
      Rep p256.C (tmv p256.C 4 base t (p256.sl RX)) (tmv p256.C 4 base t (p256.sl RY))
        (tmv p256.C 4 base t (p256.sl RZ))
        (add (mul (sv p256 base s U) (G p256.C)) (mul (sv p256 base s V) P)) := by
  have hm := unitMod_pow_two hc.p_odd (64*p256.n)
  have hOne : P256Joint.cfg.K.one<p256.C.p := by
    change 2^256%p256.C.p<p256.C.p
    exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hone : toM p256.C.p (2^(64*P256Joint.cfg.K.M.n)) P256Joint.cfg.K.one=1 := toM_cmont hc.toBaseCfgOk 1
  rw [P256Joint.points,Joint.points,Joint.window]
  apply WP.assoc
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (jointSetup_ok hc hC hT hM hTP hP hrep)) fun a ia => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (jointInitializedRun_ok hm hC hc.am3 hOne hc.onG hP
    (show sv p256 base s U<2^256 from wordsVal_lt ..)
    (show sv p256 base s V<2^256 from wordsVal_lt ..) ia.field ia.stable ia.generator)
    fun b ⟨kb,ib,_⟩ => ?_)
  refine WP.mono (jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl) hm hC hOne hone
    (by decide) ib) fun t ⟨kt,ut,_,lt,rep⟩ => ?_
  have un := jointPoint_union (jointPoint_union ia.unch (kb.unch.cover jointPoint_loop))
    (ut.cover jointPoint_finish)
  have hs := ib.field.scr.of_keepRegs kt (by decide)
  exact ⟨finalState_of_joint hM hs (kt.rd.trans (kb.regs.rd.trans ia.rd))
    (kt.wr.trans (kb.regs.wr.trans ia.wr)) un (lt _ (by decide)) (lt _ (by decide)),rep⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
