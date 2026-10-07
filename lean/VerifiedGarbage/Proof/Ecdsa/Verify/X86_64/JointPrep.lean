import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields

/-! Recode the verifier scalars while retaining its fixed data and peer point. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

theorem jointPrep_slot_apart {c : Cfg} {j : Joint.Cfg} (hn : c.n=4)
    (hK : j.K=c.winCfg PX PY BP) (hg : j.gBits=6000) {i : Nat} (hi : i<45) :
    ∀ w∈jointPrepRanges j,c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i := by
  intro w hw
  simp only [jointPrepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · left
    simp only [sl_eq,hn,hg]
    omega
  · left
    rw [hK]
    change c.sl i+8*c.n≤c.sl WB
    simp only [sl_eq,hn,WB]
    omega

theorem jointPrep_fixedOk {c : Cfg} {j : Joint.Cfg} (hn : c.n=4)
    (hK : j.K=c.winCfg PX PY BP) (hg : j.gBits=6000) : FixedOk c (jointPrepRanges j) := by
  intro w hw
  simp only [jointPrepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · right
    simp only [sl_eq,hn,hg]
    decide
  · right
    rw [hK]
    change c.sl 12≤c.sl WB
    simp only [sl_eq,hn,WB]
    decide

structure JointPrepPost (c : Cfg) (j : Joint.Cfg) (base T : Addr) (g : Reg → BitVec 64)
    {G : Point c.C} (Q : Point c.C) (row : JointGeneratorRow c.C G) (s t : State) : Prop where
  field : Inv j.K.M base size c.C.p (·∈nafSlots j.K) (winRo j.K) (tmv c.C j.K.M.n base t) t
  point : InvJ c.C (tmv c.C j.K.M.n base t j.K.P.x) (tmv c.C j.K.M.n base t j.K.P.y)
    (tmv c.C j.K.M.n base t j.K.P.z) Q
  zero : tmv c.C j.K.M.n base t j.K.zero=0
  peer : ∀ i<257,t.mem (off base (j.K.bits+i))=FastNaf.byte 5 (sv c base s V) i
  generator : ∀ i<257,t.mem (off base (j.gBits+i))=FastNaf.byte 7 (sv c base s U) i
  external : JointGenerator j c.C base T size row t
  fixed : Fixed c base g t.mem
  same : ∀ i<45,sv c base t i=sv c base s i
  keep : KeepRegs nafPrepClob s t
  unch : Unch base (jointPrepRanges j) s.mem t.mem
  syms : t.syms=s.syms

theorem jointPrepStage_ok {c : Cfg} {j : Joint.Cfg} {d : CombData}
    (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb=some d)
    (hn : c.n=4) (hw : d.w=7) (hsym : j.tsym=d.tsym)
    (hK : j.K=c.winCfg PX PY BP) (hg : j.gBits=6000) (hnp : c.C.n≤c.C.p)
    (hL : JointPrepLayout j size (c.sl U) (c.sl V)) (hF : Lay j.K.M size (·∈nafSlots j.K))
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s)
    {Q : Point c.C} (hq : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q) :
    WP isa (Joint.prep j (c.sl U) (c.sl V)) s
      (JointPrepPost c j (s₀.gpr .rcx) (s₀.syms d.tsym) g Q (jointCombRow hc hC hT hcd hn hw) s) := by
  have field := jointMid_field hc hK hnp h
  have point := jointMid_point hc hC hK h hq
  have zero := jointMid_zero hK h
  have generator := jointMid_generator hc hC hT hcd hn hw hsym hp h
  refine WP.mono_syms (jointPrepFields_ok hL hF field generator)
    fun t ⟨it,dg,dq,gt,hk,ht⟩ sy => ?_
  have pv : ∀ x∈jacCoords j.K.P,x∈winRo j.K := by
    intro x hx
    simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have sv4 (k : Nat) : sv c (s₀.gpr .rcx) s k=wordsVal s.mem (s₀.gpr .rcx) (c.sl k) 4 := by
    unfold sv
    rw [hn]
  refine ⟨it.to_tmv,it.point_tmv pv point,(it.val _ (by simp [winRo])).trans zero,?_,?_,gt,
    h.fixed.unch hc.n10 h.scr.nowrap (jointPrep_fixedOk hn hK hg) ht,?_,hk,ht,sy⟩
  · rw [sv4]
    exact dq
  · rw [sv4]
    exact dg
  · intro i hi
    exact sv_unch ht hc.n10 h.scr.nowrap hi (jointPrep_slot_apart hn hK hg hi)

end VG.Proof.Ecdsa.Verify.X86_64
