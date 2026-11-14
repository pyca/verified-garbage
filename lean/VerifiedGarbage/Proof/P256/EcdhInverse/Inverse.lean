module

import VerifiedGarbage.Proof.P256.EcdhInverse.Packed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Impl.P256.EcdhInverse
public import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
import VerifiedGarbage.Proof.P256.EcdhInverse.RawUpdate
public import VerifiedGarbage.Proof.P256.EcdhInverse.Update
import Mathlib.Tactic.Positivity
public import VerifiedGarbage.Proof.Divstep.Alg
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch
import Mathlib.Tactic.FieldSimp
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.P256.EcdhInverse.Finish
import VerifiedGarbage.Proof.P256.EcdhInverse.Extra
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-! ### `P256.EcdhInverse.Loop`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Batch`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Words`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def batchRegs : List Reg := .x19::(allocatedRegs.filter (· != .x20))

theorem words_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    {I : Divstep.IState} (hI : IInv p256.invP base I s) (hd : |I.d|≤2^30) (hf1 : I.f%2=1)
    (hz : s.gpr .x27=0) {j : Nat} (hj : 1≤j) (hj' : j<2^64)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block p256.invP.batchStart) s fun s₁ =>
      WP isa (.block Impl.P256.EcdhInverse.packed) s₁ fun t =>
      let m:=Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)
      t.gpr .x1=BitVec.ofInt 64 m.d ∧ t.gpr .x4=BitVec.ofInt 64 m.u ∧
      t.gpr .x5=BitVec.ofInt 64 m.v ∧ t.gpr .x6=BitVec.ofInt 64 m.q ∧ t.gpr .x7=BitVec.ofInt 64 m.r ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧ t.mem=s.mem ∧ KeepRegs batchRegs s t ∧ t.gpr .x27=0 := by
  refine WP.mono (batchStart_ok hs (P:=p256.invP) (by decide) (by decide) (by decide) (by decide) hj hj' h19)
    fun s₁ ⟨c19,c11,c12,c2,c3,c4,c5,c6,c7,m₁,k₁⟩ => ?_
  have low (a : Nat) (x : Int)
      (h : (wordsVal s.mem base a p256.invP.L : Int)%((2^(64*p256.invP.L):Nat):Int)=x%((2^(64*p256.invP.L):Nat):Int)) :
      word s.mem base a=BitVec.ofInt 64 x := by
    have hc := congrArg (fun z : Int => z%2^64) h
    have hdvd : (2:Int)^64 ∣ ((2^(64*p256.invP.L):Nat):Int) := by
      rw [Nat.cast_pow,Nat.cast_ofNat]; exact pow_dvd_pow 2 (by decide)
    simp only [Int.emod_emod_of_dvd _ hdvd] at hc
    have low : (wordsVal s.mem base a p256.invP.L : Int)%2^64=((word s.mem base a).toNat:Int) := by
      simp only [show p256.invP.L=5 from rfl,wordsVal]
      push_cast
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega_using []) (by have := (word s.mem base a).isLt; omega_using [])
    rw [low] at hc
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    omega_using [hc]
  refine WP.mono (packed_ok s₁ I.d I.f I.g
    (by rw [k₁.gpr _ (by decide)]; exact hI.d)
    (by rw [c2]; exact low _ _ hI.f) (by rw [c3]; exact low _ _ hI.g)
    (by rw [k₁.gpr _ (by decide)]; exact hz) hf1 (by omega_using [hd]))
    fun t ⟨d,u,v,q,r,hk⟩ => ?_
  exact ⟨d,u,v,q,r,by rw [hk.gpr _ (by decide),c19],by rw [hk.mem,m₁],
    (k₁.mono (by decide)).trans ((VG.Proof.Mont.AArch64.Keeps.regs hk).mono (by decide)),
    by rw [hk.gpr _ (by decide),k₁.gpr _ (by decide),hz]⟩
end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

def batchMemory : List (Nat × Nat) := batchW p256.invP++[(7104,576)]

private theorem word_values {m m' : Mem} {base : Addr} {a n : Nat}
    (h : ∀ i<n,word m base (a+8*i)=word m' base (a+8*i)) :
    wordsVal m base a n=wordsVal m' base a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [wordsVal]
    rw [show word m base a=word m' base a by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by omega_using [])]
    rw [ih (a:=a+8) (fun i hi => by rw [show a+8+8*i=a+8*(i+1) by omega_using []]; exact h (i+1) (by omega_using [hi]))]

theorem update_clob : ∀r∈Update.optimized.flatMap Forward.instrClob,r∈allocatedRegs.filter (· != .x20) := by
  rw [Update.rightCode.lit_eq]; decide +kernel

theorem update_writes : ∀w∈Update.optimized.flatMap Forward.instrWrites,
    ∃w'∈batchMemory,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [Update.rightCode.lit_eq]; decide +kernel

theorem update_x27 : Reg.x27∉Update.optimized.flatMap Forward.instrClob := by
  rw [Update.rightCode.lit_eq]; decide +kernel

theorem batch_ok {base : Addr} {m : Nat} (hL : InvLay p256.invP 8192)
    {s : State} (hs : Scr s base 8192) (hM : ModOkA p256.invP.M 8192 m s.mem base)
    {I : Divstep.IState} (hI : IInv p256.invP base I s)
    (hd : |I.d|≤2^30) (hf1 : I.f%2=1) (hf : |I.f|≤m) (hg : |I.g|≤m)
    (ha : |I.a|≤m) (hb : |I.b|≤m) (hz : s.gpr .x27=0)
    {j : Nat} (hj : 1≤j) (hj' : j<2^64) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa Impl.P256.EcdhInverse.batch s fun t =>
      IInv p256.invP base (Divstep.batch 59 m p256.invP.M.minv.toNat I) t ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧ KeepRegs batchRegs s t ∧
      Unch base batchMemory s.mem t.mem ∧ t.gpr .x27=0 := by
  unfold Impl.P256.EcdhInverse.batch
  refine WP.seq (WP.mono (words_ok hs hI hd hf1 hz hj hj' h19) fun a qa => ?_)
  refine WP.seq (WP.mono qa fun b ⟨bd,bu,bv,bq,br,b19,bmem,bkeep,bzero⟩ => ?_)
  have hsb := hs.of_keepRegs bkeep (by decide)
  have mb : ModOkA p256.invP.M 8192 m b.mem base := by rw [bmem]; exact hM
  have qb := raw_update_ok hL hsb mb
    (by rw [bmem]; exact hI.f) (by rw [bmem]; exact hI.g)
    (by rw [bmem]; exact hI.a) (by rw [bmem]; exact hI.b) hf1 hf hg ha hb bd bu bv bq br
  refine WP.mono (Update.refine hsb (by decide) qb) fun t ⟨u,qu,hu,kt,ut⟩ => ?_
  obtain ⟨iu,u19,ku,uu⟩ := qu
  have heq : ∀a∈[p256.invP.sF,p256.invP.sG,p256.invP.sA,p256.invP.sB],
      ∀n, n≤(if a=p256.invP.sF ∨ a=p256.invP.sG then 5 else 4) →
      wordsVal t.mem base a n=wordsVal u.mem base a n := by
    intro a ha n hn
    have hn5 : n≤5 := by split at hn <;> omega_using [hn]
    change a∈[2272,2312,2352,2384] at ha
    apply word_values
    intro i hi
    apply hu
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> simp only [Update.observe] <;>
        norm_num [show p256.invP.sF=2272 from rfl,show p256.invP.sG=2312 from rfl] at hn <;> omega_arith
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> omega_using []
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> omega_using [hn5, hi]
  have hnot1 : Reg.x1∉Update.optimized.flatMap Forward.instrClob :=
    fun hr => (Update.keepsDeltaCounter _ hr).1 rfl
  have hnot19 : Reg.x19∉Update.optimized.flatMap Forward.instrClob :=
    fun hr => (Update.keepsDeltaCounter _ hr).2 rfl
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [kt.gpr _ hnot1]; simpa only [Divstep.batch] using bd
  · rw [heq _ (by simp) _ (by decide)]; exact iu.f
  · rw [heq _ (by simp) _ (by decide)]; exact iu.g
  · rw [heq _ (by simp) _ (by decide)]; exact iu.a
  · rw [heq _ (by simp) _ (by decide)]; exact iu.b
  · rw [kt.gpr _ hnot19]; exact b19
  · exact bkeep.trans (kt.mono fun r hr => List.mem_cons_of_mem _ (update_clob r hr))
  · have h := ut.cover update_writes
    rw [bmem] at h
    exact h
  · rw [kt.gpr _ update_x27]; exact bzero

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

abbrev cfg := p256.invP

def bodyMemory : List (Nat × Nat) := invW cfg++[(7104,576)]

theorem mod_keep {base : Addr} {m : Nat} {s t : State}
    (_hs : Scr s base 8192) (hM : ModOkA cfg.M 8192 m s.mem base)
    (hU : Unch base batchMemory s.mem t.mem) : ModOkA cfg.M 8192 m t.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red,hM.call⟩
  rw [hU.wordsVal (by decide) (by decide)]
  exact hM.val

theorem packed_loop_ok {base : Addr} {m : Nat}
    (hL : InvLay cfg 8192) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA cfg.M 8192 m s.mem base) {X : Nat} (hX : X<m)
    (hm2 : m%2=1) (hm1 : 1<m)
    (hI : IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X 0) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 cfg.B) (hz : s.gpr .x27=0) :
    WP isa (.loop Impl.P256.EcdhInverse.batch (.nonzero .x .x19)) s fun t =>
      IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X cfg.B) t ∧
      KeepRegs batchRegs s t ∧ Unch base batchMemory s.mem t.mem := by
  have hmi : ((m:Int)*(cfg.M.minv.toNat:Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n:=cfg.B) (by decide)
    (Inv:=fun j t => IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X (cfg.B-j)) t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ Scr t base 8192 ∧ ModOkA cfg.M 8192 m t.mem base ∧
      KeepRegs batchRegs s t ∧ Unch base batchMemory s.mem t.mem ∧ t.gpr .x27=0)
    (fun j t hj1 hjB ⟨it,xt,st,mt,kt,ut,zt⟩ => ?_)
    (fun t ⟨it,_,_,_,kt,ut,_⟩ => ⟨by simpa only [Nat.sub_zero] using it,kt,ut⟩)
    (by decide) ⟨by rw [Nat.sub_self]; exact hI,h19,hs,hM,
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl _ _ _,hz⟩
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=m) (m:=cfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2)
    (by exact_mod_cast hm1) hmi (by omega_using []) (by exact_mod_cast hX) (cfg.B-j)
  refine WP.mono (batch_ok hL st mt it (by
    have hh : ((59*(cfg.B-j):Nat):Int)≤590 := by
      have : cfg.B=10 := by decide
      omega_using [this]
    omega_using [bd, hh]) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le)
    (by rw [abs_of_nonneg bb0]; exact bb1.le) zt hj1 (by omega_using [hjB,show cfg.B=10 from rfl]) xt)
    fun u ⟨iu,xu,ku,uu,zu⟩ => ⟨⟨?_,xu,st.of_keepRegs ku (by decide),mod_keep st mt uu,
      kt.trans ku,fun x hx => (uu x hx).trans (ut x hx),zu⟩,xu⟩
  rw [show cfg.B-(j-1)=cfg.B-j+1 by omega_using [hj1, hjB]]
  exact iu

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

def body : Prog isa := .seq (.block (([.movz .x .x27 0 0] : List Instr)++cfg.init)) <|
  .seq (.loop Impl.P256.EcdhInverse.batch (.nonzero .x .x19)) (.block cfg.finish)

def inverseMemory : List (Nat × Nat) := bodyMemory++[(7800,72)]

theorem zero27_ok (s : State) : WP isa (.block [.movz .x .x27 0 0]) s fun t =>
    t.gpr .x27=0 ∧ Keeps [.x27] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,RegUpd.gpr_write,
    ↓reduceIte,Option.some.injEq,exists_eq_left',
    show (16*0:Nat)<Size.x.bits by decide]
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [RegUpd.gpr_write,hr,↓reduceIte]

theorem body_ok {base : Addr} {m : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay cfg 8192)
    (hm2 : 2<m) (hR : UnitMod m (2^256)) {s : State}
    (hs : Scr s base 8192) (hM : ModOkA cfg.M 8192 m s.mem base)
    (hX : wordsVal s.mem base cfg.base 4<m) (hC : InvOk cfg m) :
    WP isa body s fun t => KeepRegs batchRegs s t ∧ Unch base bodyMemory s.mem t.mem ∧
      wordsVal t.mem base cfg.acc 4<m ∧
      toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal s.mem base cfg.base 4)^(m-2) := by
  have hodd : m%2=1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩|⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k,by omega_using [hk]⟩; omega_using [hm2, this]
    · omega_using [hk]
  rw [body]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (zero27_ok s) fun a ⟨az,ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  have ma : ModOkA cfg.M 8192 m a.mem base := by rw [ka.mem]; exact hM
  refine WP.mono (init_ok hL ha ma hC.B16) fun b ⟨ib,b19,kb,ub⟩ => ?_
  have hb := ha.of_keepRegs kb (by decide)
  have bz : b.gpr .x27=0 := by rw [kb.gpr _ (by decide)]; exact az
  have ub' : Unch base batchMemory a.mem b.mem := ub.cover (by decide)
  have mb := mod_keep ha ma ub'
  have hx : wordsVal a.mem base cfg.base 4<m := by rw [ka.mem]; exact hX
  refine WP.seq (WP.mono (packed_loop_ok hL hb mb hx hodd (by omega_using [hm2]) ib b19 bz)
    fun c ⟨ic,kc,uc⟩ => ?_)
  have hc := hb.of_keepRegs kc (by decide)
  have mc := mod_keep hb mb uc
  refine WP.mono (finish_power_ok hpr hT hL hm2 hR hc mc hx ic hC)
    fun t ⟨kt,ut,lt,et⟩ => ⟨?_,?_,lt,?_⟩
  · have kra : KeepRegs [.x27] s a := ⟨ka.gpr,ka.rd,ka.wr,ka.sp⟩
    exact (((kra.mono (by decide)).trans (kb.mono (by decide))).trans kc).trans (kt.mono (by decide))
  · have ub'' : Unch base bodyMemory a.mem b.mem := ub.cover (by decide)
    have uc' : Unch base bodyMemory b.mem c.mem := uc.cover (by decide)
    have ut' : Unch base bodyMemory c.mem t.mem := ut.cover (by decide)
    intro x hx
    rw [ut' x hx,uc' x hx,ub'' x hx,ka.mem]
  · change toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal a.mem base cfg.base 4)^(m-2) at et
    rw [et,ka.mem]

theorem inverse_ok {base : Addr} {m : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay cfg 8192)
    (hm2 : 2<m) (hR : UnitMod m (2^256)) {s : State}
    (hs : Scr s base 8192) (hM : ModOkA cfg.M 8192 m s.mem base)
    (hX : wordsVal s.mem base cfg.base 4<m) (hC : InvOk cfg m) :
    WP isa Impl.P256.EcdhInverse.inverse s fun t =>
      KeepRegs (powClob 4) s t ∧ Unch base inverseMemory s.mem t.mem ∧
      wordsVal t.mem base cfg.acc 4<m ∧
      toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal s.mem base cfg.base 4)^(m-2) := by
  have full : WP isa (.seq (.block Impl.P256.EcdhInverse.saveExtra)
      (.seq body (.block Impl.P256.EcdhInverse.restoreExtra))) s (fun t =>
        KeepRegs (powClob 4) s t ∧ Unch base inverseMemory s.mem t.mem ∧
        wordsVal t.mem base cfg.acc 4<m ∧
        toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
          toM m (2^256) (wordsVal s.mem base cfg.base 4)^(m-2)) := by
    refine WP.seq (WP.mono (saveExtra_ok hs (by decide)) fun a ⟨ka,ua,sa⟩ => ?_)
    have ha := hs.of_keepRegs ka (by simp)
    have ma : ModOkA cfg.M 8192 m a.mem base := by
      refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red,hM.call⟩
      rw [ua.wordsVal (by decide) (by decide)]
      exact hM.val
    have va : wordsVal a.mem base cfg.base 4=wordsVal s.mem base cfg.base 4 :=
      ua.wordsVal (by decide) (by decide)
    refine WP.seq (WP.mono (body_ok hpr hT hL hm2 hR ha ma (by rw [va]; exact hX) hC)
      fun b ⟨kb,ub,lb,eb⟩ => ?_)
    have hb := ha.of_keepRegs kb (by decide)
    have sb := savedExtra_keep sa ub (by decide)
    refine WP.mono (restoreExtra_ok hb (by decide) sb) fun t ⟨kt,vt⟩ => ⟨?_,?_,?_,?_⟩
    · exact (restoreExtra_frame ka kb kt vt).mono (by decide)
    · intro x hx
      rw [kt.mem,ub x (fun w hw => hx w (List.mem_append_left _ hw)),
        ua x (hx (7800,72) (List.mem_append_right _ (by simp)))]
    · rw [kt.mem]; exact lb
    · rw [kt.mem,eb,va]
  simpa only [Impl.P256.EcdhInverse.inverse,body,Impl.P256.EcdhInverse.P,
    Impl.P256.EcdhInverse.c,cfg,WP.seq_iff (M:=isa),WP.block_append_iff (M:=isa)] using full

end VG.Proof.P256.EcdhInverse
