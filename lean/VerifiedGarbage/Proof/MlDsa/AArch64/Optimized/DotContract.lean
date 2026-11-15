module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemory
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBatch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBank
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFiveSlice
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMiddle
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
public import VerifiedGarbage.Proof.MlDsa.FusedInverseContract
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlDsa.AArch64.Optimized.DotCore`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotFive`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.DotBank`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

/-- All eight inputs are loaded before any inverse layer starts. Memory and
input pointers are unchanged, and each lane is the original exact product. -/
theorem inverseDotLoads_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State} (hc : ProductConstants s)
    (hr : ∀ j<8,∀ k<n, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs inverseProductOps) s t → ProductConstants t →
      (∀ j<8, ∀ e<4, vword (t.v (Inverse.vr j)) e=dotResult s n (16*j) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (inverseDotLoads n ++ rest)) s Q := by
  have hnDistinct : (inverseProductOps.map Prod.fst).Nodup := by decide
  have hd d off (hm : (d,off)∈inverseProductOps) :
      d∉productTemps ∧ d≠.v30 ∧ d≠.v31 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    exact inverseProduct_safe (List.mem_range.mp hj)
  have hi d off (hm : (d,off)∈inverseProductOps) : ∀ k<n,
      (1024*k+off)%16=0 ∧ 1024*k+off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    have hj' := List.mem_range.mp hj
    intro k hk
    refine ⟨?_,by omega_using [hn7, hj', hk],hr j hj' k hk⟩
    omega_using []
  have eqcode : inverseProductOps.flatMap (fun p => dotLoad n p.1 p.2)=inverseDotLoads n := by
    simp only [inverseProductOps,inverseDotLoads,List.flatMap_map]
  rw [← eqcode]
  refine dotBatch_ok hn inverseProductOps hnDistinct hd hc hi fun t ht ct vt => k t ht ct ?_
  intro j hj e he
  exact vt _ _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩) e he

end VG.Proof.MlDsa.AArch64.Optimized

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized (inverseDotLoads)

theorem dotFirstArithmetic_eq :
    VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstArithmetic=fiveCode++firstStores := by
  kernel_rfl

theorem dot_initial_regs (j : Fin 8) :
    (regs 0)[j.val]=VG.Impl.MlDsa.AArch64.Optimized.Inverse.vr j.val := by
  decide +revert +kernel

/-- Raw product loads feed the inverse directly in registers. -/
def dotFiveCode (n : Nat) : List Instr := inverseDotLoads n ++ fiveCode ++ firstStores

theorem dotFive_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) (u : Nat) {s : State} {v : Vector (BitVec 128) 8}
    (hv : ∀ j : Fin 8, ∀ e<4, vword v[j.val] e=dotResult s n (16*j.val) e)
    (hc : ProductConstants s)
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (hr : ∀ j<8,∀ k<n, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+16*j)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t
      (writeBank (fiveValues u v) (s.gpr .x0) 16 s.mem)) → WP isa (.block rest) t Q) :
    WP isa (.block (dotFiveCode n ++ rest)) s Q := by
  simp only [dotFiveCode,List.append_assoc]
  refine inverseDotLoads_ok hn hn7 hc hr fun s₁ hc₁ _ hv₁ => ?_
  have hc₁' : VChg runRegs s s₁ := hc₁.mono (by decide)
  have hb : Bank s₁ (regs 0) v := by
    intro i
    apply vec_ext
    intro e he
    have hr := dot_initial_regs i
    rw [hr,hv₁ i.val i.isLt e he,hv i e he]
  refine five_ok u hb (hp.frame (hc₁.mono (by decide))) (hl.frame hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  rw [firstStores_eq]
  refine storeBank_ok (regs 7) 16 .x0 (by intro i; omega_using []) hb₂ ?_ fun t hm => ?_
  · intro i
    simpa only [hc₂.wr,hc₂.gpr,hc₁.wr,hc₁.gpr] using hw i
  · refine k t ⟨s₂,(hc₁'.trans hc₂).mono (by simp),?_⟩
    simpa only [hc₂.mem,hc₂.gpr,hc₁.mem,hc₁.gpr] using hm

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


/-! ## From `DotLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized (DotInverse.firstAdvance)

def dotLoopRegs : List Reg := [.x0,.x1,.x11,.x13,.x14]

theorem dotAdvance_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance) s fun t =>
      ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧ t.gpr .x11=s.gpr .x11-1 ∧
        t.gpr .x13=s.gpr .x13+128 ∧ t.gpr .x14=s.gpr .x14+128 ∧ t.mem=s.mem) ∧
        Keep dotLoopRegs s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dotFirstBlock_eq (count : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count=
      dotFiveCode count++VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock,dotFirstArithmetic_eq,
    dotFiveCode,List.append_assoc]

/-- The complete first pass, retaining exact input/output cursors. -/
theorem dotLoop_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hc : s.gpr .x11=8) (hq : ProductConstants s)
    (hrt : ∀off,off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀j<8,∀k<count,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*k+16*j)) 16)
    (hw : ∀u<8,∀i : Fin 8,InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count)) (.nonzero .x .x11)) s fun t =>
      Keep dotLoopRegs s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count 8 := by
  rw [dotFirstBlock_eq]
  let I := fun u t => Keep dotLoopRegs s t ∧ ProductConstants t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.gpr .x13=s.gpr .x13+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x14=s.gpr .x14+BitVec.ofNat 64 (128*u) ∧
    t.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hp13,hp14,hm⟩
    have ht' : InverseTable.Words t.mem (s.gpr .x1) := by
      rw [hm]
      exact tableWords_frame ht (dotPass_frame (by omega_arith)) (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hd)
    have hrt' : ∀off,off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    have hqv : ∀e<4,vword (t.v .v31) e=8380417#32 := by
      intro e he; rw [hqt.qv,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
      rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl
    refine dotFive_ok hn hn7 u (v:=dotBankValues t count) (fun j e he => dotBankValues_word t count j he)
      hqt (packed_tableRoots hu ht' hrt' hp1 hqv) (local_tableRoots hu ht' hrt' hp1 hqv)
      ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro j hj k hkc; simpa only [hk.rd,hk.wr,hp13,hp14] using hr u hu j hj k hkc
    · intro i; simpa only [hk.wr,hp0] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (dotAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hc₂,hp₁₃,hp₁₄,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_,?_,?_⟩,?_⟩
      · constructor
        · rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]; exact hqt.qv
        · rw [hvec₂,hv₁.v,hv.get .v30 (by decide)]; exact hqt.qiv
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₁₃,hk₁.get .x13,hp13]
        rw [show 128*(u+1)=128*u+128 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₁₄,hk₁.get .x14,hp14]
        rw [show 128*(u+1)=128*u+128 by omega_arith,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hm₂,hv₁.mem,← dotMemoryBank_eq]
        simp only [hm,hp0,hp13,hp14,dotPassMem]
      · rw [hc₂,hk₁.get .x11]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)

def dotInitRegs : List Reg := [.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11]

theorem dotSetup_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) s fun t =>
      Keep dotInitRegs s t ∧ t.mem=s.mem ∧ t.gpr .x11=8 ∧ ProductConstants t := by
  change WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++
    Instr.vop (.dup .s4 .v30 .x10)::
      (VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v31 8380417++firstSetup))) s _
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x10 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d:=.v30) rfl fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v31 8380417) fun c hc => ?_
  refine WP.mono (firstSetup_ok c) fun t ⟨⟨⟨h11,htm⟩,htk⟩,htv⟩ => ?_
  refine ⟨(((hk.trans hb.chg.keep).trans (constKeep_keep hc.1 (by decide))).trans htk).mono,
    htm.trans (hc.1.mem.trans (hb.mem.trans hm)),h11,?_,?_⟩
  · rw [htv,hc.2]; rfl
  · rw [htv,hc.1.vec .v30 (by decide),hb.v,ha]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def dotCoreRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11,.x12,.x13,.x14]

def dotInverseMem (m : Mem) (p a b : Addr) (count : Nat) : Mem :=
  finalPassMem (dotPassMem m p a b count 8) p (HighPack.repeatedWord 8380417) 8

theorem dotCore_eq (count : Nat) : VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count=
    .seq (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) (.seq
      (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count)) (.nonzero .x .x11))
      (.seq (.block middleCode) (.loop (.block (finalSliceCode++finalAdvance)) (.nonzero .x .x12)))) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core
  rw [finalBody_eq]
  rfl

/-- The standalone inverse executes the selected two-pass memory transform.
Only table and buffer accessibility are required at this machine boundary. -/
theorem dotCore_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hra : ∀ off, off+16≤1024*count → InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16)
    (hrb : ∀ off, off+16≤1024*count → InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    (hr : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀ off, off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧ t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count := by
  rw [dotCore_eq]
  apply WP.seq
  refine WP.mono (dotSetup_ok s) fun a ⟨hka,hma,h11,hqa⟩ => ?_
  have ha0 : a.gpr .x0=s.gpr .x0 := hka.get .x0 (by decide)
  have ha1 : a.gpr .x1=s.gpr .x1 := hka.get .x1 (by decide)
  have ha13 : a.gpr .x13=s.gpr .x13 := hka.get .x13 (by decide)
  have ha14 : a.gpr .x14=s.gpr .x14 := hka.get .x14 (by decide)
  apply WP.seq
  refine WP.mono (dotLoop_ok hn hn7 (s := a) ?_ ?_ h11 hqa ?_ ?_ ?_) fun b ⟨hkb,hqb,hb0,hb1,_,_,hmb⟩ => ?_
  · simpa only [hma,ha1] using ht
  · simpa only [ha0,ha1] using hd
  · simpa only [hka.rd,hka.wr,ha1] using hrt
  · intro u hu j hj k hk
    simp only [hka.rd,hka.wr,ha13,ha14,BitVec.add_assoc,← BitVec.ofNat_add]
    exact ⟨hra _ (by omega_arith),hrb _ (by omega_arith)⟩
  · intro u hu i
    simp only [hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hw _ (by omega_arith)
  · have hb0' : b.gpr .x0=s.gpr .x0+1024 := by simpa only [ha0] using hb0
    have hb1' : b.gpr .x1=s.gpr .x1+3840 := by simpa only [ha1] using hb1
    have hmb' : b.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count 8 := by simpa only [hma,ha0,ha13,ha14] using hmb
    have htb : InverseTable.Words b.mem (s.gpr .x1) := by
      rw [hmb']
      exact tableWords_frame ht (dotPass_frame (by decide)) (by
        intro r hr
        have he := List.mem_singleton.mp hr
        subst r
        exact hd)
    have hqbLane : ∀e<4,vword (b.v .v31) e=8380417#32 := by
      intro e he
      rw [hqb.qv]
      exact HighPack.repeatedWord_lane _ he
    apply WP.seq
    refine WP.mono (middle_ok (s := b) htb hb1' ?_ hqbLane) fun c ⟨hkc,hmc,hc0,hc2,hc12,hfc,hsc⟩ => ?_
    · intro off hoff
      simp only [hkb.rd,hkb.wr,hka.rd,hka.wr,hb1']
      change InRegions (s.rd++s.wr) ((s.gpr .x1+BitVec.ofNat 64 3840)+BitVec.ofNat 64 off) 16
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      apply hrt
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
      omega_arith
    · have hc0' : c.gpr .x0=s.gpr .x0 := by rw [hc0,hb0']; bv_omega
      have hc2' : c.gpr .x2=s.gpr .x0 := by rw [hc2,hb0']; bv_omega
      have hqv : c.v .v31=HighPack.repeatedWord 8380417 := (by apply VG.AArch64.vec_ext; intro e he; rw [hfc.q e he,HighPack.repeatedWord_lane _ he])
      refine WP.mono (finalLoop_ok hfc hsc hc12 ?_ ?_) fun t ⟨hkt,_,_,hmt⟩ => ?_
      · intro u hu i
        simp only [hkc.rd,hkc.wr,hkb.rd,hkb.wr,hka.rd,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hr _ (by omega_arith)
      · intro u hu i
        simp only [hkc.wr,hkb.wr,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hw _ (by omega_arith)
      · refine ⟨(((hka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
        · rw [hkt.get .x0 (by decide),hc0']
        · simpa only [dotInverseMem,hmc,hmb',hc2',hqv] using hmt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ### `MlDsa.AArch64.Optimized.DotMemoryValues`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

theorem dotMemoryBank_word (m : Mem) (a b : Addr) (count : Nat) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (dotMemoryBank m a b count)[j.val] e=dotMemoryWord m a b count (16*j.val) e := by
  simp only [dotMemoryBank,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl

theorem dotMemoryWord_offset (m : Mem) (a b : Addr) (count u j e : Nat) (he : e<4) :
    dotMemoryWord m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count (16*j) e=
      centeredDot (fun k => coeffAt m (a+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e))
        (fun k => coeffAt m (b+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e)) count := by
  unfold dotMemoryWord
  congr 1 <;> funext k <;>
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he] <;>
    simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add] <;> congr 3 <;> omega_using []

theorem dotPass_bank_original {m : Mem} {p a b : Addr} {count u : Nat} (hu : u<8)
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    dotMemoryBank (dotPassMem m p a b count u) (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count=
    dotMemoryBank m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [dotMemoryBank_word _ _ _ _ ⟨i,hi⟩ he,dotMemoryBank_word _ _ _ _ ⟨i,hi⟩ he,
    dotMemoryWord_offset _ _ _ _ _ _ _ he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  apply centeredDot_congr
  · intro k hk
    exact coeffAt_frame (dotPass_frame (by omega_using [hu])) (by
      intro r hr; have hr' := List.mem_singleton.mp hr; subst r; exact ha k hk)
      (by change 32*u+4*i+e<256; omega_using [hu, hi, he])
  · intro k hk
    exact coeffAt_frame (dotPass_frame (by omega_using [hu])) (by
      intro r hr; have hr' := List.mem_singleton.mp hr; subst r; exact hb k hk)
      (by change 32*u+4*i+e<256; omega_using [hu, hi, he])

def dotMemStep (m : Mem) (p a b : Addr) (count u : Nat) : Mem :=
  writeBank (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
    (b+BitVec.ofNat 64 (128*u)) count)) (coeffAddr p (32*u)) 16 m

theorem dotPassMem_step (m : Mem) (p a b : Addr) (count u : Nat) :
    dotPassMem m p a b count (u+1)=dotMemStep (dotPassMem m p a b count u) p a b count u := by
  simp only [dotPassMem,dotMemStep,coeffAddr,show 4*(32*u)=128*u by omega_using []]

theorem dotMemStep_at (m : Mem) (p a b : Addr) (count : Nat) {u : Nat} (hu : u<8)
    (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (dotMemStep m p a b count u) p (32*u+4*i.val+e)=
      vword (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
        (b+BitVec.ofNat 64 (128*u)) count))[i.val] e := by
  exact writeBank_coeff_at _ m p (start:=32*u) (step:=4) (by decide) (by omega_using [hu]) i he

theorem dotMemStep_outside (m : Mem) (p a b : Addr) (count : Nat) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k<32*u ∨ 32*(u+1)≤k) :
    coeffAt (dotMemStep m p a b count u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start:=32*u) (step:=4) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hout]

theorem dotPass_processed {m : Mem} {p a b : Addr} {count u k : Nat}
    (ha : ∀j<count,(polyRegion (a+BitVec.ofNat 64 (1024*j))).Disjoint (polyRegion p))
    (hb : ∀j<count,(polyRegion (b+BitVec.ofNat 64 (1024*j))).Disjoint (polyRegion p))
    (hu : u≤8) (hk : k<n) (hp : k/32<u) :
    coeffAt (dotPassMem m p a b count u) p k=
      vword (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count))[(k%32)/4]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [dotPassMem_step]
    by_cases he : k/32=u
    · have hi : (k%32)/4<8 := by omega_using []
      have hidx : 32*u+4*((k%32)/4)+k%4=k := by omega_using [he]
      have hx := dotMemStep_at (dotPassMem m p a b count u) p a b count (by omega_using [hu] : u<8)
        ⟨(k%32)/4,hi⟩ (e:=k%4) (by omega_using [])
      rw [hidx,dotPass_bank_original (by omega_using [hu]) ha hb] at hx
      simpa only [he,
        getElem!_pos (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
          (b+BitVec.ofNat 64 (128*u)) count)) ((k%32)/4) hi] using hx
    · rw [dotMemStep_outside _ _ _ _ _ (by omega_using [hu]) hk (by omega_using [he])]
      exact ih (by omega_using [hu]) (by omega_using [hp, he])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


/-! ## From `DotStatic.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlKem.AArch64 (mov)

def dotFamilyRegion (p : Addr) (count : Nat) : Region := ⟨p,1024*count⟩

theorem dotInverseMem_frame (m : Mem) (p a b : Addr) (count : Nat) :
    Frame [outputRegion p] m (dotInverseMem m p a b count) :=
  (dotPass_frame (m:=m) (p:=p) (a:=a) (b:=b) (count:=count) (by decide)).trans
    (finalPass_frame (by decide))

theorem dotCore_words_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (htr : tableRegion (s.gpr .x1)∈s.rd++s.wr)
    (ha : dotFamilyRegion (s.gpr .x13) count∈s.rd++s.wr)
    (hb : dotFamilyRegion (s.gpr .x14) count∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count := by
  refine WP.mono (dotCore_ok hn hn7 ht hsep ?_ ?_ ?_ ?_ ?_) fun t ⟨hk,hp,hm⟩ => ?_
  · intro off ho; exact ⟨_,htr,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,ha,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,hb,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,List.mem_append_right _ hw,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · intro off ho; exact ⟨_,hw,VG.Offset.contains_base _ ho (by omega_arith)⟩
  · exact ⟨hk,hp,by rw [hm]; exact dotInverseMem_frame _ _ _ _ _,hm⟩

theorem dotStaticInit_ok (s : State) :
    WP isa (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_INV_FOLDED" ∧ t.gpr .x13=s.gpr .x1 ∧
        t.gpr .x14=s.gpr .x2 ∧ t.mem=s.mem) ∧ Keep [.x1,.x13,.x14] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold mov
  arun [exec_adrSym]
  rfl

/-- Exact selected dot4/5/7 inverse machine endpoint. The unused scratch
argument remains untouched; writes are confined to the output polynomial. -/
theorem dotStaticCode_words_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED"))
    (htr : tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr)
    (ha : dotFamilyRegion (s.gpr .x1) count∈s.rd++s.wr)
    (hb : dotFamilyRegion (s.gpr .x2) count∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) count := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode
  refine WP.seq (WP.mono (dotStaticInit_ok s) fun a ⟨⟨hp1,hp13,hp14,hm⟩,hk⟩ => ?_)
  have ht' : InverseTable.Words a.mem (a.gpr .x1) := by simpa only [hp1,hm] using ht.words
  refine WP.mono (dotCore_words_ok hn hn7 ht' ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hpt,hft,hmt⟩ => ?_
  · simpa only [hp1,hk.rd,hk.wr] using htr
  · simpa only [hp13,hk.rd,hk.wr] using ha
  · simpa only [hp14,hk.rd,hk.wr] using hb
  · simpa only [hk.get .x0 (by decide),hk.wr] using hw
  · simpa only [hp1,hk.get .x0 (by decide)] using hsep
  · exact ⟨(hk.trans hkt).mono,hpt.trans (hk.get .x0 (by decide)),
      by simpa only [hm,hk.get .x0 (by decide)] using hft,
      by simpa only [hm,hp13,hp14,hk.get .x0 (by decide)] using hmt⟩

theorem dotCoreKeep_abi {s t : State} (h : Keep dotCoreRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `FusedRepresentation.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem positiveReduced_iff {m : Mem} {p : Addr} :
    PositiveReduced m p ↔ PosPolyIs m p (polyAt m p) :=
  ⟨fun h => ⟨h,rfl⟩,fun h => h.bound⟩

/-- The inverse cancels the internal Montgomery factor for a whole matrix row. -/
theorem inverse_dotNTT (f g : Nat → Poly) (count : Nat) :
    montgomeryNttInv (Representation.encode true (dotPoly f g count))=
      nttInv (dotNTT f g count) :=
  Representation.inverse_encode true _

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `DotMemoryField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem dotMemoryBank_bound {m : Mem} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k)) :
    BankBound (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count) 8380417 := by
  intro j e he
  rw [dotMemoryBank_word _ _ _ _ j he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_arith
  have hbnd := centeredDot_bound _ _ hc
    (fun k hkc => (hf k hkc).bound _ hk) (fun k hkc => (hg k hkc).bound _ hk)
  exact ⟨hbnd.1,Int.le_of_lt hbnd.2⟩

theorem dotMemoryBank_field {m : Mem} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k)) :
    InnerBankField u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count) (Representation.encode true (dotPoly f g count)) := by
  intro j e he
  rw [dotMemoryBank_word _ _ _ _ j he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega_arith
  refine centeredDot_field _ _ f g hc (fun k hkc => (hf k hkc).bound _ hk)
    (fun k hkc => (hg k hkc).bound _ hk) hk ?_ ?_
  · intro k hkc; rw [ofInt_nat_eq,← polyAt_get _ _ hk,(hf k hkc).value]; rfl
  · intro k hkc; rw [ofInt_nat_eq,← polyAt_get _ _ hk,(hg k hkc).value]; rfl

theorem dotPass_field {m : Mem} {p a b : Addr} {f g : Nat → Poly} {count : Nat}
    (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k))
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    SignedPolyIs (dotPassMem m p a b count 8) p
      (InverseTraversal.run InverseTraversal.localSchedule (Representation.encode true (dotPoly f g count)))
      (-268173344) 268173344 := by
  have bank (u : Nat) (hu : u<8) := fiveValues_field _ _ hu
    (dotMemoryBank_bound hu hc hf hg) (dotMemoryBank_field hu hc hf hg)
  have hout (k : Nat) (hk : k<n) :
      -268173344≤(coeffAt (dotPassMem m p a b count 8) p k).toInt ∧
      (coeffAt (dotPassMem m p a b count 8) p k).toInt≤268173344 ∧
      ofInt (coeffAt (dotPassMem m p a b count 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.localSchedule (Representation.encode true (dotPoly f g count)))[k]! := by
    have hu : k/32<8 := by change k<256 at hk; omega_arith
    have hi : (k%32)/4<8 := by omega_arith
    have he : k%4<4 := by omega_arith
    rw [dotPass_processed ha hb (by decide) hk hu,
      getElem!_pos (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count)) ((k%32)/4) hi]
    have hbank := bank (k/32) hu
    refine ⟨(hbank.1 ⟨(k%32)/4,hi⟩ _ he).1,(hbank.1 ⟨(k%32)/4,hi⟩ _ he).2,?_⟩
    have hv := hbank.2 ⟨(k%32)/4,hi⟩ _ he
    have hidx : 32*(k/32)+4*((k%32)/4)+k%4=k := by omega_arith
    simp only [Traversal.innerLoc] at hv
    rw [hidx] at hv
    have hcoord := InverseTraversal.prefix_selected InverseTraversal.localSlice (fun k => k/32) 8
      (fun u hu => InverseTraversal.local_supported ⟨u,hu⟩)
      (Representation.encode true (dotPoly f g count)) hk hu
    exact hv.trans hcoord.symm
  exact ⟨fun k hk => ⟨(hout k hk).1,(hout k hk).2.1⟩,fun k hk => (hout k hk).2.2⟩

theorem dotInverseMem_field {m : Mem} {p a b : Addr} {f g : Nat → Poly} {count : Nat}
    (hc : count≤7)
    (hf : ∀k<count,PosPolyIs m (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs m (b+BitVec.ofNat 64 (1024*k)) (g k))
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    PolyIs (dotInverseMem m p a b count) p (nttInv (dotNTT f g count)) := by
  have hp := finalPass_field (dotPass_field hc hf hg ha hb) (qv:=HighPack.repeatedWord 8380417)
    (fun e he => HighPack.repeatedWord_lane _ he)
  simpa only [dotInverseMem,InverseTraversal.traversal_montgomery,inverse_dotNTT] using hp

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def dotK (count : Nat) : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    dotFamilyRegion (s.gpr .x1) count∈s.rd++s.wr ∧ dotFamilyRegion (s.gpr .x2) count∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    (dotFamilyRegion (s.gpr .x1) count).Disjoint (outputRegion (s.gpr .x0)) ∧
    (dotFamilyRegion (s.gpr .x2) count).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧
    (∀j<count,PositiveReduced s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j))) ∧
    (∀j<count,PositiveReduced s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j)))
  post s t := PolyIs t.mem (s.gpr .x0) (nttInv (dotNTT
    (fun j => polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j => polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) count))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧
    s.sp=t.sp ∧ s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem dot_pre {count : Nat} {s : State}
    (h : (dotInverseContract count (abi.withConsts inverseConsts)).pre s) : (dotK count).pre s := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,_,ht,hw,rest⟩ := h
  have hrd : s.rd=[dotFamilyRegion (s.gpr .x1) count,dotFamilyRegion (s.gpr .x2) count,
      tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    have he : count*256*4=1024*count := by omega_arith
    rw [he]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hrd]; simp,by rw [hrd]; simp,
    by rw [hw]; simp [outputRegion],?_,?_,?_,?_,?_,?_⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · have hh : (outputRegion (s.gpr .x0)).Disjoint (dotFamilyRegion (s.gpr .x1) count) := by
      dsimp only [outputRegion,dotFamilyRegion]; grind only
    exact hh.symm
  · have hh : (outputRegion (s.gpr .x0)).Disjoint (dotFamilyRegion (s.gpr .x2) count) := by
      dsimp only [outputRegion,dotFamilyRegion]; grind only
    exact hh.symm
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))
  · grind only
  · grind only

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
