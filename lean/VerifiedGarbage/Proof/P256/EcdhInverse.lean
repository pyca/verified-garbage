module

public import VerifiedGarbage.Impl.P256.EcdhInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ObservedInputs
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Divstep.Bound
public import VerifiedGarbage.Proof.Divstep.Tc
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.P256.EcdhInverse
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ObservedInputs
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! P-256's field inversion: the generic batches, their update register-allocated. -/

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.P256.EcdhInverse (extra saveExtra restoreExtra body inverse)

abbrev cfg : InvCfg := Impl.Ecdsa.AArch64.p256.invP

/-! ### The allocated update -/

def original : List Instr := Impl.P256.EcdhInverse.updateRaw
def optimized : List Instr := Impl.P256.EcdhInverse.update

/-- The words of `f`, `g`, `a` and `b`; the staging slots are not observed. -/
def observe (off : Nat) : Prop := 2272≤off ∧ off<2416
instance (off : Nat) : Decidable (observe off) := inferInstanceAs (Decidable (2272≤off ∧ off<2416))

/-- The registers the update writes. -/
def updateRegs : List Reg :=
  [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,
   .x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]
def bodyRegs : List Reg := .x1::.x19::updateRegs

def batchWrites : List (Nat × Nat) := batchW cfg ++ [(7104,576)]
def bodyWrites : List (Nat × Nat) := invW cfg ++ [(7104,576)]

materialize_value leftCode := original
materialize_value rightCode := optimized
forward_state bundle :=
  let ns := (buildPairFrom 8192 original optimized (matrixNodes 8192) (matrixEnv 8192)).getD ⟨.empty,.empty⟩
  (ns,(evalData (certDom ns) 8192 original (matrixEnv 8192)).getD (.empty,.empty,none),
    (evalData (certDom ns) 8192 optimized (matrixEnv 8192)).getD (.empty,.empty,none))
noncomputable def nodes := bundle.1

theorem valid : CertValid nodes := valid_of_validK (by decide +kernel)

theorem inputs : Inputs nodes 8192 := inputs_of_allBelow (by decide +kernel)

theorem matrixInputs :
    nodes.nodes.lookup 1025=some (.input 8192) ∧ nodes.nodes.lookup 1026=some (.input 8200) ∧
    nodes.nodes.lookup 1027=some (.input 8208) ∧ nodes.nodes.lookup 1028=some (.input 8216) := by decide +kernel

noncomputable def left : Env Nat := fromData (matrixEnv 8192) bundle.2.1
noncomputable def right : Env Nat := fromData (matrixEnv 8192) bundle.2.2

theorem evalLeft : eval (certDom nodes) 8192 original (matrixEnv 8192)=some left := by
  rw [leftCode.lit_eq]
  exact eval_of_dataK (by kernel_rfl)

theorem evalRight : eval (certDom nodes) 8192 optimized (matrixEnv 8192)=some right := by
  rw [rightCode.lit_eq]
  exact eval_of_dataK (by kernel_rfl)

theorem same : ∀ off,observe off → off%8=0 → off+8≤8192 → left.slot off=right.slot off :=
  fun off hv _ _ => same_of_sameK observe (by decide +kernel) off hv

noncomputable def checked : CheckedObserved 8192 observe original optimized where
  nodes := nodes
  valid := valid
  initial := matrixEnv 8192
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same

theorem initial_rel (s : State) (base : Addr) :
    Rel (nodeVal nodes (matrixInput 8192 s base)) base 8192 (matrixEnv 8192) s :=
  matrix_initial_rel inputs matrixInputs.1 matrixInputs.2.1 matrixInputs.2.2.1 matrixInputs.2.2.2 s base

 theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  rw [leftCode.lit_eq]; exact bound_of_listAllK (by decide +kernel)

 theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  rw [rightCode.lit_eq]; exact bound_of_listAllK (by decide +kernel)

 theorem keepsDeltaCounter : ∀ r∈optimized.flatMap instrClob,r≠.x1 ∧ r≠.x19 := by
  rw [rightCode.lit_eq]
  decide +kernel

theorem update_refine {s : State} {base : Addr} {cap : Nat} (hs : Scr s base cap) (hcap : 8192≤cap)
    {Q : State → Prop} (hq : WP isa (.block original) s Q) :
    WP isa (.block optimized) s fun t => ∃ u,Q u ∧
      (∀ off,observe off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧
      VG.Proof.Mont.AArch64.KeepRegs (optimized.flatMap instrClob) s t ∧
      VG.Proof.Weierstrass.Unch base (optimized.flatMap instrWrites) s.mem t.mem :=
  checked.refine (matrixInput 8192 s base) (by decide) hs (initial_rel s base)
    (fun i hi => Nat.le_trans (leftBound i hi) hcap) (fun i hi => Nat.le_trans (rightBound i hi) hcap) hq

/-! ### A batch and the loop -/

private theorem wp_both {c : Prog isa} {s : State} {P Q : State → Prop}
    (hp : WP isa c s P) (hq : WP isa c s Q) : WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨tr,t,ht,hp⟩ := hp
  obtain ⟨tr',t',ht',hq⟩ := hq
  obtain ⟨rfl,rfl⟩ := ht.det ht'
  exact ⟨_,_,ht,hp,hq⟩

private theorem word_values {m m' : Mem} {base : Addr} {a n : Nat}
    (h : ∀ i<n,word m base (a+8*i)=word m' base (a+8*i)) :
    wordsVal m base a n=wordsVal m' base a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [wordsVal]
    rw [show word m base a=word m' base a by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by omega_arith)]
    rw [ih (a:=a+8) (fun i hi => by rw [show a+8+8*i=a+8*(i+1) by omega_arith]; exact h (i+1) (by omega_arith))]

 theorem update_clob : ∀ r∈optimized.flatMap Forward.instrClob,
    r∈updateRegs := by
  rw [rightCode.lit_eq]
  decide +kernel

 theorem update_writes : ∀ w∈optimized.flatMap Forward.instrWrites,
    ∃ w'∈batchWrites,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [rightCode.lit_eq]
  decide +kernel

/-- Allocating the update preserves the divstep invariant, delta and loop counter;
only the explicit allocator spill area and register set widen the internal frame. -/
theorem allocatedBatch_ok {base : Addr} {size m : Nat} (hsize : 8192≤size)
    (hL : InvLay cfg size) {s : State} (hs : Scr s base size)
    (hM : ModOkA cfg.M size m s.mem base) {I : Divstep.IState}
    (hI : IInv cfg base I s)
    (hd : |I.d|≤2^30) (hf1 : I.f%2=1) (hf : |I.f|≤m) (hg : |I.g|≤m)
    (ha : |I.a|≤m) (hb : |I.b|≤m) {j : Nat} (hj : 1≤j) (hj' : j<2^64)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa Impl.P256.EcdhInverse.batch s fun t =>
      IInv cfg base (Divstep.batch 59 m cfg.M.minv.toNat I) t ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧
      KeepRegs bodyRegs s t ∧ Unch base batchWrites s.mem t.mem := by
  have hb0 := batch_ok hL hs hM hI hd hf1 hf hg ha hb hj hj' h19
  have hw := words_ok hL hs hI hd hf1 hj hj' h19
  rw [InvCfg.batch] at hb0
  rw [Impl.P256.EcdhInverse.batch]
  refine WP.seq (WP.mono (wp_both (WP.seq_iff.mp hb0) hw) fun a ⟨qa,wa⟩ => ?_)
  refine WP.seq (WP.mono (wp_both (WP.seq_iff.mp qa) wa) fun b ⟨qb,wb⟩ => ?_)
  obtain ⟨bd,bu,bv,bq,br,b19,bmem,bkeep⟩ := wb
  have hsb := hs.of_keepRegs bkeep (by decide)
  refine WP.mono (update_refine hsb hsize qb) fun t ⟨u,qu,hu,kt,ut⟩ => ?_
  obtain ⟨iu,u19,ku,uu⟩ := qu
  have heq : ∀ a∈[cfg.sF,cfg.sG,cfg.sA,cfg.sB],
      ∀ n≤5,a+8*n≤2416 → wordsVal t.mem base a n=wordsVal u.mem base a n := by
    intro a ha n hn hb
    change a∈[2272,2312,2352,2384] at ha
    apply word_values
    intro i hi
    apply hu
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> refine ⟨?_,?_⟩ <;> omega_arith
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> omega_arith
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> omega_arith
  have hnot1 : Reg.x1∉optimized.flatMap Forward.instrClob :=
    fun hr => (keepsDeltaCounter _ hr).1 rfl
  have hnot19 : Reg.x19∉optimized.flatMap Forward.instrClob :=
    fun hr => (keepsDeltaCounter _ hr).2 rfl
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · rw [kt.gpr _ hnot1]
    simpa only [Divstep.batch] using bd
  · rw [heq _ (by simp) _ (by decide) (by decide)]; exact iu.f
  · rw [heq _ (by simp) _ (by decide) (by decide)]; exact iu.g
  · rw [heq _ (by simp) _ (by decide) (by decide)]; exact iu.a
  · rw [heq _ (by simp) _ (by decide) (by decide)]; exact iu.b
  · rw [kt.gpr _ hnot19]; exact b19
  · exact (bkeep.mono (by decide)).trans (kt.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (update_clob r hr)))
  · have h := ut.cover update_writes
    rw [bmem] at h
    exact h

/-- The inversion modulus lies outside both the arithmetic workspace and allocator spills. -/
theorem mod {base : Addr} {size m : Nat} {s t : State}
    (hs : Scr s base size) (hM : ModOkA cfg.M size m s.mem base)
    (hU : Unch base batchWrites s.mem t.mem) : ModOkA cfg.M size m t.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red, hM.call⟩
  rw [hU.wordsVal (by decide) (by omega_using [hM.mo,hs.nowrap])]
  exact hM.val

 theorem batch_frame {base : Addr} {s t : State}
    (hU : Unch base batchWrites s.mem t.mem) : Unch base bodyWrites s.mem t.mem := by
  apply hU.cover
  decide

 theorem loop_ok {base : Addr} {size m B : Nat} (hsize : 8192≤size)
    (hL : InvLay cfg size) {s : State} (hs : Scr s base size)
    (hM : ModOkA cfg.M size m s.mem base) {X : Nat} (hX : X<m)
    (hm2 : m%2=1) (hm1 : 1<m) (hB1 : 1≤B) (hB : B<2^16)
    (hI : IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X 0) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 B) :
    WP isa (.loop Impl.P256.EcdhInverse.batch (.nonzero .x .x19)) s fun t =>
      IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X B) t ∧
      KeepRegs bodyRegs s t ∧ Unch base batchWrites s.mem t.mem := by
  have hmi : ((m : Int)*(cfg.M.minv.toNat : Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n:=B) (by omega_arith)
    (Inv:=fun j t => IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X (B-j)) t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ Scr t base size ∧ ModOkA cfg.M size m t.mem base ∧
      KeepRegs bodyRegs s t ∧ Unch base batchWrites s.mem t.mem)
    (fun j t hj1 hjB ⟨it,xt,st,mt,kt,ut⟩ => ?_)
    (fun t ⟨it,_,_,_,kt,ut⟩ => ⟨by simpa only [Nat.sub_zero] using it,kt,ut⟩)
    hB1 ⟨by rw [Nat.sub_self]; exact hI,h19,hs,hM,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl _ _ _⟩
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=m) (m:=cfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2)
    (by exact_mod_cast hm1) hmi (by omega_arith) (by exact_mod_cast hX) (B-j)
  refine WP.mono (allocatedBatch_ok hsize hL st mt it (by
    have hh : ((59*(B-j) : Nat) : Int)≤59*2^16 := by exact_mod_cast (Nat.mul_le_mul_left 59 (by omega_arith : B-j≤2^16))
    omega_arith) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le)
    (by rw [abs_of_nonneg bb0]; exact bb1.le) hj1 (by omega_arith) xt)
    fun u ⟨iu,xu,ku,uu⟩ => ⟨⟨?_,xu,st.of_keepRegs ku (by decide),mod st mt uu,
      kt.trans ku,fun x hx => (uu x hx).trans (ut x hx)⟩,xu⟩
  rw [show B-(j-1)=B-j+1 by omega_arith]
  exact iu

/-! ### The whole inversion -/

theorem body_ok {base : Addr} {m : Nat} [NeZero m] (hpr : IsPrime m) (hT : InvToM m)
    (hL : InvLay cfg 8192) (hm2 : 2 < m) (hR : UnitMod m (2^256)) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA cfg.M 8192 m s.mem base) (hX : wordsVal s.mem base cfg.base 4<m) (hC : InvOk cfg m) :
    WP isa body s fun t =>
      KeepRegs bodyRegs s t ∧ Unch base bodyWrites s.mem t.mem ∧
      wordsVal t.mem base cfg.acc 4<m ∧
      toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal s.mem base cfg.base 4) ^ (m-2) := by
  have hodd : m%2=1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩ | ⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k,by omega_arith⟩
      omega_arith
    · omega_arith
  have hm256 : m≤2^256 := by
    have h : m<2^(64*4) := hM.val ▸ wordsVal_lt s.mem base cfg.M.mo cfg.M.n
    omega_using [h]
  rw [Impl.P256.EcdhInverse.body]
  refine WP.seq (WP.mono (init_ok hL hs hM (by decide)) fun a ⟨ia,a19,ka,ua⟩ => ?_)
  have ua' : Unch base batchWrites s.mem a.mem := ua.cover (by decide)
  have ha := hs.of_keepRegs ka (by decide)
  have ma := mod hs hM ua'
  refine WP.seq (WP.mono (loop_ok (by decide) hL ha ma hX hodd (by omega_using [hm2]) (B:=10) (by decide) (by decide)
    ia a19) fun b ⟨ib,kb,ub⟩ => ?_)
  have hb := ha.of_keepRegs kb (by decide)
  have done : (Divstep.invRun 59 m cfg.M.minv.toNat (wordsVal s.mem base cfg.base 4) 10).g=0 := by
    have hd := (Divstep.invRun_dfg (N:=59) (p:=(m:Int))
      (m:=cfg.M.minv.toNat) (x:=(wordsVal s.mem base cfg.base 4 : Nat)) (by exact_mod_cast hodd) 10).1
    have hz := (Divstep.divsteps_590 (by exact_mod_cast hodd) (Int.natCast_nonneg _)
      (by exact_mod_cast hX.le) (by exact_mod_cast hm256 : (m:Int)≤2^256) (by decide : 590≤59*10)).1
    rw [←hd] at hz
    exact hz
  refine WP.mono (finish_early_ok hpr hT hL hm2 hR hb (mod ha ma ub) hX ib done hC.C hC.Cpos hC.Cn)
    fun t ⟨kt,ut,lt,et⟩ => ⟨(ka.mono (by decide)).trans (kb.trans (kt.mono (by decide))),?_,lt,et⟩
  intro x hx
  have cover : ∀ {m m' : Mem},Unch base batchWrites m m' → Unch base bodyWrites m m' :=
    fun h => h.cover (by decide)
  rw [(ut.cover (by decide) : Unch base bodyWrites _ _) x hx,cover ub x hx,cover ua' x hx]

def extraRegs : List Reg := extra.map Prod.fst

theorem save_ok {s : State} {base : Addr} (hs : Scr s base 8192) :
    WP isa (.block saveExtra) s fun t =>
      KeepRegs [] s t ∧ Unch base [(7800,72)] s.mem t.mem ∧ Spill.Saved base s.gpr extra t.mem := by
  refine WP.mono (Spill.save_wp (b:=.x0) (l:=extra) (by decide) (fun p hp => hs.st (by
    have h : ∀ p∈extra,p.2+8≤8192 := by decide
    exact h p hp))) fun t h => ⟨⟨?_,h.rd,h.wr,h.sp⟩,?_,?_⟩
  · intro r _; exact congrFun h.gpr r
  · rw [h.mem,hs.x0]
    intro x hx
    have h' := hx (7800,72) (by simp)
    change (((((((((s.mem.writeW (off base 7800) (s.gpr .x21)).writeW (off base 7808) (s.gpr .x22)).writeW
      (off base 7816) (s.gpr .x23)).writeW (off base 7824) (s.gpr .x24)).writeW (off base 7832) (s.gpr .x25)).writeW
      (off base 7840) (s.gpr .x26)).writeW (off base 7848) (s.gpr .x27)).writeW (off base 7856) (s.gpr .x28)).writeW
      (off base 7864) (s.gpr .x30)) x=s.mem x
    dsimp only at h'
    rw [(writeW_outside _ base (d:=7864) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7856) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7848) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7840) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7832) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7824) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7816) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7808) _ (by decide)) x (by omega_using [h']),
      (writeW_outside _ base (d:=7800) _ (by decide)) x (by omega_using [h'])]
  · rw [h.mem,hs.x0]; exact Spill.saveMem_saved (by decide) _ _ _

theorem restore_ok {s : State} {base : Addr} {g : Reg → BitVec 64}
    (hs : Scr s base 8192) (hsv : Spill.Saved base g extra s.mem) :
    WP isa (.block restoreExtra) s fun t =>
      Keeps extraRegs s t ∧ ∀ r∈extraRegs,t.gpr r=g r := by
  refine WP.mono (Spill.restore_wp hs.x0 (l:=extra) (by decide) (by decide)
    (fun p hp => by
      rw [←hs.x0]
      apply hs.ld
      have hh : ∀ p∈extra,p.2+8≤8192 := by decide
      exact hh p hp) hsv) fun t h => ⟨⟨h.other,h.mem,h.rd,h.wr,h.sp⟩,?_⟩
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact h.gpr p hp

def inverseWrites : List (Nat × Nat) := bodyWrites ++ [(7800,72)]

/-- The inversion, keeping every register but the field operations'. -/
theorem inverse_ok {base : Addr} {m : Nat} [NeZero m] (hpr : IsPrime m) (hT : InvToM m)
    (hL : InvLay cfg 8192) (hm2 : 2 < m) (hR : UnitMod m (2^256)) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA cfg.M 8192 m s.mem base) (hX : wordsVal s.mem base cfg.base 4<m) (hC : InvOk cfg m) :
    WP isa inverse s fun t =>
      KeepRegs (powClob 4) s t ∧ Unch base inverseWrites s.mem t.mem ∧
      wordsVal t.mem base cfg.acc 4<m ∧
      toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal s.mem base cfg.base 4) ^ (m-2) := by
  rw [Impl.P256.EcdhInverse.inverse]
  refine WP.seq (WP.mono (save_ok hs) fun a ⟨ka,ua,sa⟩ => ?_)
  have ha := hs.of_keepRegs ka (by simp)
  have ma : ModOkA cfg.M 8192 m a.mem base := by
    refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red,hM.call⟩
    rw [ua.wordsVal (by decide) (by omega_using [hM.mo,hs.nowrap])]
    exact hM.val
  have va : wordsVal a.mem base cfg.base 4=wordsVal s.mem base cfg.base 4 :=
    ua.wordsVal (by decide) (by have := hs.nowrap; change 576+8*4≤2^64; omega_using [])
  refine WP.seq (WP.mono (body_ok hpr hT hL hm2 hR ha ma (by rw [va]; exact hX) hC) fun b ⟨kb,ub,lb,eb⟩ => ?_)
  have hb := ha.of_keepRegs kb (by decide)
  have sb : Spill.Saved base s.gpr extra b.mem := by
    intro p hp
    have hbd : ∀ p∈extra,7800≤p.2 ∧ p.2+8≤7872 := by decide
    have hw : ∀ w∈bodyWrites,w.1+w.2≤7800 ∨ 7872≤w.1 := by decide
    change word b.mem base p.2=_
    rw [ub.word (fun w hm => by have := hw w hm; have := hbd p hp; omega_arith)
      (by have := hbd p hp; omega_using [this])]
    exact sa p hp
  refine WP.mono (restore_ok hb sb) fun t ⟨kt,vt⟩ => ⟨⟨fun r hr => ?_,kt.rd.trans (kb.rd.trans ka.rd),
    kt.wr.trans (kb.wr.trans ka.wr),kt.sp.trans (kb.sp.trans ka.sp)⟩,?_,?_,?_⟩
  · by_cases he : r∈extraRegs
    · exact vt r he
    · have hn : r∉bodyRegs := fun h => (show ∀ r∈bodyRegs,r∈extraRegs ∨ r∈powClob 4 by decide) r h |>.elim he hr
      rw [kt.gpr r he,kb.gpr r hn,ka.gpr r (by simp)]
  · intro x hx
    rw [kt.mem,ub x (fun w hw => hx w (List.mem_append_left _ hw)),
      ua x (fun w hw => hx w (List.mem_append_right _ hw))]
  · rw [kt.mem]; exact lb
  · rw [kt.mem,eb,va]

end VG.Proof.P256.EcdhInverse
