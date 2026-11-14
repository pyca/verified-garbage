module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoad
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `MlDsa.AArch64.Optimized.PairedPartition`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedVec`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask minMask)

theorem reduce_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀t,VChg [.v25,.v24] s t → (∀e<4,vword (t.v .v24) e=reduceWord (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Paired.reduce++rest)) s Q := by
  refine wp_vop (d := .v25) rfl fun a ha => wp_vop (d := .v25) rfl fun b hb =>
    wp_vop (d := .v24) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,vword_mapWords3 _ _ _ _ he,hb.get .v24 (by decide),ha.get .v24 (by decide),
      hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v31 (by decide),ha.get .v31 (by decide),hc e he,hq e he]
    rfl

theorem norm_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v25,.v30] s t → (∀e<4,vword (t.v .v30) e=
      vword (s.v .v30) e ||| normMask (vword (s.v .v24) e)
        (vword (s.v .v9) e) (vword (s.v .v10) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Paired.norm++rest)) s Q := by
  refine wp_vop (d := .v25) rfl fun a ha => wp_vop (d := .v25) rfl fun b hb =>
    wp_vop (d := .v25) rfl fun c hc => wp_vop (d := .v30) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg |>.mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v]
    simp only [vword,BitVec.extractLsb'_or]
    change vword (c.v .v30) e ||| vword (c.v .v25) e=_
    rw [hc.get .v30 (by decide),hb.get .v30 (by decide),ha.get .v30 (by decide),
      hc.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v10 (by decide),ha.get .v10 (by decide),ha.v,VG.AArch64.vword_map2 _ _ _ he,minMask]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


/-! ## From `PairedRawNorm.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask)

def rawNorm (raw : VReg) : List Instr := ([.vop (.mov .v24 raw)] : List Instr) ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.reduce ++ VG.Impl.MlDsa.AArch64.Optimized.Paired.norm

theorem rawNorm_ok (raw : VReg) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀t,VChg [.v24,.v25,.v30] s t →
      (∀e<4,vword (t.v .v24) e=reduceWord (vword (s.v raw) e)) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (reduceWord (vword (s.v raw) e)) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (rawNorm raw++rest)) s Q := by
  unfold rawNorm
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_vop (d:=.v24) rfl fun a ha => ?_
  refine reduce_ok (by intro e he; rw [ha.get .v31 (by decide)]; exact hq e he)
    (by intro e he; rw [ha.get .v8 (by decide)]; exact hc e he) fun b hb hv => ?_
  have hh : VChg [.v24,.v25] s b := (ha.chg.trans hb).mono (by decide)
  refine norm_ok fun t ht hn => ?_
  refine k t ((hh.trans ht).mono (by decide)) ?_ ?_
  · intro e he
    rw [ht.get .v24 (by decide),hv e he,ha.v]
  · intro e he
    rw [hn e he,hh.get .v30 (by decide),hh.get .v9 (by decide),hh.get .v10 (by decide),hv e he,ha.v]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintVec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (hintWord word_or word_not)

def hintVector : List Instr :=
 [.vop (.sub .s4 .v25 .v11 .v24),.vop (.sub .s4 .v28 .v24 .v12),
  .vop (.logic .orr .v25 .v25 .v28),.vop (.shift .sshr .s4 .v25 .v25 31),
  .vop (.cmeq .s4 .v28 .v24 .v12),.vop (.cmeq .s4 .v26 .v26 .v13),
  .vop (.logic .bic .v28 .v28 .v26),.vop (.logic .orr .v25 .v25 .v28),
  .vop (.shift .ushr .s4 .v25 .v25 31)]

theorem hintVector_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hn : ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : ∀e<4,vword (s.v .v13) e=0)
    (k : ∀t,VChg [.v25,.v28,.v26] s t → (∀e<4,vword (t.v .v25) e=
      hintWord (vword (s.v .v11) e) (vword (s.v .v24) e) (vword (s.v .v26) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintVector++rest)) s Q := by
  refine wp_vop (d:=.v25) rfl fun a ha => wp_vop (d:=.v28) rfl fun b hb =>
    wp_vop (d:=.v25) rfl fun c hc => wp_vop (d:=.v25) rfl fun d hd =>
    wp_vop (d:=.v28) rfl fun f hf => wp_vop (d:=.v26) rfl fun g hg =>
    wp_vop (d:=.v28) rfl fun h hh => wp_vop (d:=.v25) rfl fun i hi =>
    wp_vop (d:=.v25) rfl fun t ht => ?_
  have hk : VChg [.v25,.v28,.v26] s t :=
    ((((((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans hf.chg).trans hg.chg).trans hh.chg).trans hi.chg).trans ht.chg).mono (by decide)
  refine k t hk ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hi.v,word_or,
    hh.get .v25 (by decide),hg.get .v25 (by decide),hf.get .v25 (by decide),hd.v,
    VG.AArch64.vword_map2 _ _ _ he,hc.v,word_or,hb.get .v25 (by decide),ha.v,
    VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
    ha.get .v24 (by decide),ha.get .v12 (by decide),hn e he,
    hh.v,Inverse.word_and,word_not _ he,hg.v,VG.AArch64.vword_map2 _ _ _ he,
    hf.get .v26 (by decide),hd.get .v26 (by decide),hc.get .v26 (by decide),
    hb.get .v26 (by decide),ha.get .v26 (by decide),
    hf.get .v13 (by decide),hd.get .v13 (by decide),hc.get .v13 (by decide),
    hb.get .v13 (by decide),ha.get .v13 (by decide),hz e he,
    hg.get .v28 (by decide),hf.v,VG.AArch64.vword_map2 _ _ _ he,
    hd.get .v24 (by decide),hc.get .v24 (by decide),hb.get .v24 (by decide),ha.get .v24 (by decide),
    hd.get .v12 (by decide),hc.get .v12 (by decide),hb.get .v12 (by decide),ha.get .v12 (by decide),hn e he]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZ.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep laneVector laneVector_word reduceWord normMask)

def zInput (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
  reduceWord (vword (s.v raw) e+vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e)
def zLane (raw : VReg) (off : Nat) : List Instr :=
  ([.ldrq .v27 .x15 off,.vop (.add .s4 .v24 raw .v27)] : List Instr) ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.reduce ++ [.strq .v24 .x15 off] ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.norm

theorem zLane_ok {s : State} (raw : VReg) (hne : raw≠.v27) {off : Nat}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v24,.v25,.v27,.v30] s t →
      t.mem=s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (laneVector (zInput s raw off)) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (zInput s raw off e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (zLane raw off++rest)) s Q := by
  unfold zLane
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun a ha => wp_vop (d:=.v24) rfl fun b hb => ?_
  have hpre : VChg [.v27,.v24] s b := ha.chg.trans hb.chg
  refine reduce_ok (by intro e he; rw [hpre.get .v31 (by decide)]; exact hq e he)
    (by intro e he; rw [hpre.get .v8 (by decide)]; exact hc e he) fun c hcc hv => ?_
  have hh : VChg [.v24,.v25,.v27] s c := (hpre.trans hcc).mono (by decide)
  have hval : c.v .v24=laneVector (zInput s raw off) := by
    apply vec_ext
    intro e he
    rw [laneVector_word _ he,hv e he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.get raw hne,ha.v]
    rfl
  refine wp_strq ho rfl (by simpa only [hh.wr,hh.gpr] using hw) fun d hd => ?_
  refine norm_ok fun t ht hn => ?_
  refine k t ?_ ?_ ?_
  · exact (((StepKeep.ofChg hh (by decide)).trans (StepKeep.ofMem hd)).trans
      (StepKeep.ofChg ht (by decide))).mono (by decide)
  · rw [ht.mem,hd.mem,hh.mem,hh.gpr,hval]
  · intro e he
    rw [hn e he,hd.v,hh.get .v30 (by decide),hh.get .v9 (by decide),
      hh.get .v10 (by decide),hval,laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintHead.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask hintWord)

def hintOutput (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
  hintWord (vword (s.v .v11) e)
    (reduceWord (vword (s.v raw) e)+vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e)
    (vword (s.mem.read (s.gpr .x16+BitVec.ofNat 64 off) 16) e)

def hintHead (raw : VReg) (off : Nat) : List Instr := rawNorm raw ++
  ([.ldrq .v27 .x15 off,.ldrq .v26 .x16 off,.vop (.add .s4 .v24 .v24 .v27)] : List Instr) ++ hintVector

theorem hintHead_ok (raw : VReg) {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hh : InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (hn : ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : ∀e<4,vword (s.v .v13) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v24,.v25,.v26,.v27,.v28,.v30] s t →
      (∀e<4,vword (t.v .v25) e=hintOutput s raw off e) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (reduceWord (vword (s.v raw) e)) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintHead raw off++rest)) s Q := by
  unfold hintHead
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine rawNorm_ok raw hq hc fun a ha hv hnorm => ?_
  refine wp_ldrq ho rfl (by simpa only [ha.rd,ha.wr,ha.gpr] using hl) fun b hb => ?_
  have hbb : VChg [.v24,.v25,.v27,.v30] s b := (ha.trans hb.chg).mono (by decide)
  refine wp_ldrq ho rfl (by simpa only [hbb.rd,hbb.wr,hbb.gpr] using hh) fun c hcc => ?_
  refine wp_vop (d:=.v24) rfl fun d hd => ?_
  have hdd : VChg [.v24,.v25,.v26,.v27,.v30] s d := ((hbb.trans hcc.chg).trans hd.chg).mono (by decide)
  refine hintVector_ok
    (by intro e he; rw [hdd.get .v12 (by decide),hdd.get .v11 (by decide)]; exact hn e he)
    (by intro e he; rw [hdd.get .v13 (by decide)]; exact hz e he) fun t ht hout => ?_
  refine k t ((hdd.trans ht).mono (by decide)) ?_ ?_
  · intro e he
    rw [hout e he,hdd.get .v11 (by decide),hd.v,VG.AArch64.vword_map2 _ _ _ he,
      hcc.get .v24 (by decide),hb.get .v24 (by decide),hv e he,hcc.get .v27 (by decide),hb.v,
      ha.mem,ha.gpr,hd.get .v26 (by decide),hcc.v,hbb.mem,hbb.gpr]
    rfl
  · intro e he
    rw [ht.get .v30 (by decide),hd.get .v30 (by decide),hcc.get .v30 (by decide),
      hb.get .v30 (by decide),hnorm e he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHint.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_strq wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector laneVector_word reduceWord normMask)

def hintLane (raw : VReg) (off : Nat) : List Instr := hintHead raw off ++
  [.strq .v25 .x15 off,.vop (.add .s4 .v14 .v14 .v25)]

theorem hintLane_ok (raw : VReg) {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hh : InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (hn : ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : ∀e<4,vword (s.v .v13) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepFrame [.v14,.v24,.v25,.v26,.v27,.v28,.v30] s t →
      t.mem=s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (laneVector (hintOutput s raw off)) →
      (∀e<4,vword (t.v .v14) e=vword (s.v .v14) e+hintOutput s raw off e) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (reduceWord (vword (s.v raw) e)) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintLane raw off++rest)) s Q := by
  unfold hintLane
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine hintHead_ok raw ho hl hh hq hc hn hz fun a ha hv hm => ?_
  have vv : a.v .v25=laneVector (hintOutput s raw off) := by
    apply vec_ext; intro e he; rw [laneVector_word _ he,hv e he]
  refine wp_strq ho rfl (by simpa only [ha.wr,ha.gpr] using hw) fun b hb => ?_
  refine wp_vop (d:=.v14) rfl fun t ht => ?_
  refine k t ?_ ?_ ?_ ?_
  · exact (((StepFrame.ofChg ha).trans (StepFrame.ofMem hb)).trans
      (StepFrame.ofChg ht.chg)).mono (by decide)
  · rw [ht.chg.mem,hb.mem,ha.mem,ha.gpr,vv]
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,ha.get .v14 (by decide),hv e he]
  · intro e he
    rw [ht.get .v30 (by decide),hb.v,hm e he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPartition.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem zCheck_eq (g p j : Nat) : check .z g p j=zLane (vr (8*p+j)) (1024*p+128*j) := rfl

theorem hCheck_eq (g p j : Nat) : check .h g p j=hintLane (vr (8*p+j)) (1024*p+128*j) := rfl

theorem finalPrefix_eq : finalBody.take (finalBody.length-finalStore.length-2)=finalLoads++finalArithmetic := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckStep.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector laneVector_word)

def checkRegs : List VReg := [.v14,.v24,.v25,.v26,.v27,.v28,.v30]
def checkCode (hint : Bool) (raw : VReg) (off : Nat) : List Instr :=
  if hint then hintLane raw off else zLane raw off

theorem checkData_ext {a b : CheckData} (hm : a.mem=b.mem) (hf : a.flags=b.flags) (hc : a.count=b.count) : a=b := by
  cases a; cases b; cases hm; cases hf; cases hc; rfl

theorem checkStep_ok (hint : Bool) (raw : VReg) (hne : raw≠.v27)
    {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hh : hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (hn : hint=true → ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : hint=true → ∀e<4,vword (s.v .v13) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepFrame checkRegs s t → dataAt t=checkStep hint (s.v raw)
      (s.gpr .x15+BitVec.ofNat 64 off) (s.gpr .x16+BitVec.ofNat 64 off) (constantsAt s) (dataAt s) →
      WP isa (.block rest) t Q) : WP isa (.block (checkCode hint raw off++rest)) s Q := by
  cases hint with
  | false =>
    refine zLane_ok raw hne ho hl hw hq hc fun t ht hm hf => k t ((StepFrame.ofKeep ht).mono (by decide)) ?_
    apply checkData_ext
    · exact hm
    · apply vec_ext
      intro e he
      simpa only [checkStep,dataAt,constantsAt,Bool.false_eq_true,ite_false,laneVector_word _ he,zInput] using hf e he
    · exact ht.vec .v14 (by decide)
  | true =>
    refine hintLane_ok raw ho hl (hh rfl) hw hq hc (hn rfl) (hz rfl) fun t ht hm hcount hf => k t (ht.mono (by decide)) ?_
    apply checkData_ext
    · exact hm
    · apply vec_ext
      intro e he
      simpa only [checkStep,dataAt,constantsAt,ite_true,laneVector_word _ he] using hf e he
    · apply vec_ext
      intro e he
      simpa only [checkStep,dataAt,constantsAt,ite_true,laneVector_word _ he,hintOutput] using hcount e he

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckRun.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

structure CheckReady (hint : Bool) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v31) e=8380417#32
  bias : ∀e<4,vword (s.v .v8) e=4194304#32
  neg : hint=true → ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e
  zero : hint=true → ∀e<4,vword (s.v .v13) e=0

theorem CheckReady.frame {hint : Bool} {s t : State} (h : CheckReady hint s)
    (hf : StepFrame checkRegs s t) : CheckReady hint t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v12 (by decide),hf.vec .v11 (by decide)]; exact h.neg
  · rw [hf.vec .v13 (by decide)]; exact h.zero

theorem constantsAt_frame {s t : State} (hf : StepFrame checkRegs s t) : constantsAt t=constantsAt s := by
  unfold constantsAt
  rw [hf.vec .v11 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem Banks.checkFrame {s t : State} {v : Values} (h : Banks s v) (hf : StepFrame checkRegs s t) : Banks t v := by
  intro p j
  rw [hf.vec _ ((show ∀p:Fin 2,∀j:Fin 8,(bankRegs p)[j.val]∉checkRegs by decide) p j)]
  exact h p j

def checkRunCode (hint : Bool) (js : List (Fin 2 × Fin 8)) : List Instr :=
  js.flatMap fun (p,j) => checkCode hint (bankRegs p)[j.val] (1024*p.val+128*j.val)

theorem checkRun_ok (hint : Bool) (js : List (Fin 2 × Fin 8))
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hc : CheckReady hint s)
    (hr : ∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,StepFrame checkRegs s t →
      dataAt t=checkRun hint v (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) js →
      WP isa (.block rest) t Q) :
    WP isa (.block (checkRunCode hint js++rest)) s Q := by
  induction js generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ rfl
  | cons op js ih =>
    simp only [checkRunCode,List.flatMap_cons,List.append_assoc]
    have hn : (bankRegs op.1)[op.2.val]≠.v27 :=
      (show ∀p:Fin 2,∀j:Fin 8,(bankRegs p)[j.val]≠.v27 by decide) op.1 op.2
    refine checkStep_ok hint _ hn (by constructor <;> omega_using [])
      (hr op.1 op.2).1 (hr op.1 op.2).2.1 (hr op.1 op.2).2.2
      hc.q hc.bias hc.neg hc.zero fun a ha hda => ?_
    refine ih (hv.checkFrame ha) (hc.frame ha) ?_ fun t ht hdt => ?_
    · simpa only [ha.rd,ha.wr,ha.gpr] using hr
    · refine k t ((ha.trans ht).mono (by simp)) ?_
      rw [hdt,ha.gpr,constantsAt_frame ha,hda,hv op.1 op.2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def allChecks : List (Fin 2 × Fin 8) := (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j => (p,j)
def finalCheckCode (hint : Bool) : List Instr := finalLoads++finalArithmetic++checkRunCode hint allChecks

def rawPairAt (s : State) : Values := fun p => Inverse.rawFinalValues (readPair s.mem (s.gpr .x2) 128 p)
def finalCheckData (hint : Bool) (s : State) : CheckData :=
  checkRun hint (rawPairAt s) (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) allChecks

def finalCheckRegs : List VReg := stageRunRegs++checkRegs

theorem checkReady_arithmetic {hint : Bool} {s t : State} (h : CheckReady hint s)
    (hf : VChg stageRunRegs s t) : CheckReady hint t := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hf.get .v31 (by decide)]; exact h.q
  · rw [hf.get .v8 (by decide)]; exact h.bias
  · rw [hf.get .v12 (by decide),hf.get .v11 (by decide)]; exact h.neg
  · rw [hf.get .v13 (by decide)]; exact h.zero

theorem constantsAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : constantsAt t=constantsAt s := by
  unfold constantsAt
  rw [hf.get .v11 (by decide),hf.get .v9 (by decide),hf.get .v10 (by decide)]

theorem dataAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : dataAt t=dataAt s := by
  unfold dataAt
  rw [hf.mem,hf.get .v30 (by decide),hf.get .v14 (by decide)]

theorem finalCheck_ok (hint : Bool) {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382)) (hc : CheckReady hint s)
    (hw : ∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,StepFrame finalCheckRegs s t → dataAt t=finalCheckData hint s →
      WP isa (.block rest) t Q) :
    WP isa (.block (finalCheckCode hint++rest)) s Q := by
  simp only [finalCheckCode,List.append_assoc]
  refine finalLoadArithmetic_ok hr ht hs hc.q fun a ha va => ?_
  refine checkRun_ok hint allChecks va (checkReady_arithmetic hc ha) ?_ fun t hct hd => ?_
  · simpa only [ha.rd,ha.wr,ha.gpr] using hw
  · refine k t ((StepFrame.ofChg ha).trans hct) ?_
    unfold finalCheckData rawPairAt
    simpa only [ha.gpr,constantsAt_arithmetic ha,dataAt_arithmetic ha] using hd

end VG.Proof.MlDsa.AArch64.Optimized.Paired
