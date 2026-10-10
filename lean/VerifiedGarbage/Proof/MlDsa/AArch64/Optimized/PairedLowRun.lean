import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStageRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalCheck
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalAdvance
import VerifiedGarbage.Proof.Framework.Offset

/-! ## `PairedLowStep` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep laneVector laneVector_word)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

theorem lowPairStep_ok {g : Nat} (hg : IsG g) {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (rd0 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (rd1 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,StepKeep (lowPairClobs r q) s v →
      dataAt v=lowPairStep g (s.v r) (s.v q)
        (s.gpr .x15+BitVec.ofNat 64 off) (s.gpr .x15+BitVec.ofNat 64 (off+128))
        (s.gpr .x16+BitVec.ofNat 64 off) (s.gpr .x16+BitVec.ofNat 64 (off+128))
        (lowConstantsAt s) (dataAt s) → WP isa (.block rest) v Q) :
    WP isa (.block (lowPairBlocks g r q off++rest)) s Q := by
  refine lowPair_ok hg hr hq hrq ho rd0 rd1 wh0 wh1 wl0 wl1 hmod hc h11 h12 h13 h14
    fun v ha hb la lb hv hm hha hhb hla hlb hf => k v hv ?_
  have vecEq (v : BitVec 128) (f : Nat → BitVec 32)
      (h : ∀e<4,vword v e=f e) : v=laneVector f := by
    apply vec_ext
    intro e he
    rw [laneVector_word _ he]
    exact h e he
  have eha := vecEq ha _ hha
  have ehb := vecEq hb _ hhb
  have ela := vecEq la _ hla
  have elb := vecEq lb _ hlb
  rw [eha,ehb,ela,elb] at hm
  rw [ela,elb] at hf
  apply checkData_ext
  · simpa only [lowPairWrites,lowPairStep,lowInputValues,lowInputWord,lowConstantsAt,dataAt] using hm
  · apply vec_ext
    intro e he
    simpa only [lowPairStep,lowInputValues,lowInputWord,lowConstantsAt,dataAt,laneVector_word _ he] using hf e he
  · have rn : r≠.v14 := by intro he; exact hr (by simp [he,lowReserved])
    have qn : q≠.v14 := by intro he; exact hq (by simp [he,lowReserved])
    exact hv.vec .v14 (by simp [lowPairClobs,Ne.symm rn,Ne.symm qn])
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPending` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

abbrev LowIndex := Fin 2 × Fin 4
def lowRaw0 (i : LowIndex) : VReg := vr (8*i.1.val+2*i.2.val)
def lowRaw1 (i : LowIndex) : VReg := vr (8*i.1.val+2*i.2.val+1)
def lowValue0 (v : Values) (i : LowIndex) : BitVec 128 := (v i.1)[2*i.2.val]
def lowValue1 (v : Values) (i : LowIndex) : BitVec 128 := (v i.1)[2*i.2.val+1]
def lowOff (i : LowIndex) : Nat := 1024*i.1.val+256*i.2.val

def LowPending (s : State) (v : Values) (is : List LowIndex) : Prop :=
  ∀i∈is,s.v (lowRaw0 i)=lowValue0 v i ∧ s.v (lowRaw1 i)=lowValue1 v i

theorem Banks.lowPending {s : State} {v : Values} (h : Banks s v) (is : List LowIndex) : LowPending s v is := by
  intro i hi
  constructor
  · simpa only [bankRegs,Vector.getElem_ofFn,lowRaw0,lowValue0] using h i.1 ⟨2*i.2.val,by omega⟩
  · simpa only [bankRegs,Vector.getElem_ofFn,lowRaw1,lowValue1,Nat.add_assoc] using h i.1 ⟨2*i.2.val+1,by omega⟩

theorem low_raw_keep (i j : LowIndex) (hne : i≠j) :
    lowRaw0 j∉lowPairClobs (lowRaw0 i) (lowRaw1 i) ∧
    lowRaw1 j∉lowPairClobs (lowRaw0 i) (lowRaw1 i) := by
  rcases i with ⟨p,i⟩
  rcases j with ⟨q,j⟩
  revert p i q j
  decide

theorem LowPending.next {s t : State} {v : Values} {i : LowIndex} {is : List LowIndex}
    (h : LowPending s v (i::is)) (hn : i∉is)
    (hf : StepKeep (lowPairClobs (lowRaw0 i) (lowRaw1 i)) s t) : LowPending t v is := by
  intro j hj
  have hne : i≠j := by intro he; exact hn (he ▸ hj)
  have hk := low_raw_keep i j hne
  rw [hf.vec _ hk.1,hf.vec _ hk.2]
  exact h j (List.mem_cons_of_mem _ hj)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReady` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.Round VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowRunRegs : List VReg := stageRunRegs++[.v30]

structure LowReady (g : Nat) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v31) e=8380417#32
  bias : ∀e<4,vword (s.v .v8) e=4194304#32
  c11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127
  c12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g)
  c13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g)
  c14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g)

theorem LowReady.frame {g : Nat} {s t : State} (h : LowReady g s)
    (hf : StepFrame lowRunRegs s t) : LowReady g t := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v11 (by decide)]; exact h.c11
  · rw [hf.vec .v12 (by decide)]; exact h.c12
  · rw [hf.vec .v13 (by decide)]; exact h.c13
  · rw [hf.vec .v14 (by decide)]; exact h.c14

theorem lowConstantsAt_frame {s t : State} (hf : StepFrame lowRunRegs s t) : lowConstantsAt t=lowConstantsAt s := by
  unfold lowConstantsAt
  rw [hf.vec .v15 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem lowClobs_subset (i : LowIndex) : lowPairClobs (lowRaw0 i) (lowRaw1 i)⊆lowRunRegs := by
  rcases i with ⟨p,j⟩
  revert p j
  decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRun` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

def lowRun (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) : List LowIndex → CheckData
  | [] => d
  | i::is => lowRun g v out aux c (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d) is

def lowRunCode (g : Nat) (is : List LowIndex) : List Instr :=
  is.flatMap fun i => lowPairBlocks g (lowRaw0 i) (lowRaw1 i) (lowOff i)

theorem lowRun_ok {g : Nat} (hg : IsG g) (is : List LowIndex) (hn : is.Nodup)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : LowPending s v is) (hc : LowReady g s)
    (hr : ∀i:LowIndex,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i+128)) 16)
    (k : ∀t,StepFrame lowRunRegs s t → dataAt t=lowRun g v (s.gpr .x15) (s.gpr .x16)
      (lowConstantsAt s) (dataAt s) is → WP isa (.block rest) t Q) :
    WP isa (.block (lowRunCode g is++rest)) s Q := by
  induction is generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ rfl
  | cons i is ih =>
    simp only [lowRunCode,List.flatMap_cons,List.append_assoc]
    have hh := lowPair_registers i.1.isLt i.2.isLt
    have ho := lowPair_offsets i.1.isLt i.2.isLt
    refine lowPairStep_ok hg hh.1 hh.2.1 hh.2.2 ⟨ho.1,ho.2.1⟩
      (hr i).1 (hr i).2.1 (hr i).2.2.1 (hr i).2.2.2.1 (hr i).2.2.2.2.1 (hr i).2.2.2.2.2
      hc.q hc.bias hc.c11 hc.c12 hc.c13 hc.c14 fun a ha hda => ?_
    have haf : StepFrame lowRunRegs s a := (StepFrame.ofKeep ha).mono (lowClobs_subset i)
    refine ih (List.nodup_cons.mp hn).2 (hv.next (List.nodup_cons.mp hn).1 ha) (hc.frame haf) ?_
      fun t ht hdt => ?_
    · simpa only [haf.rd,haf.wr,haf.gpr] using hr
    · refine k t ((haf.trans ht).mono (by simp)) ?_
      have hvi := hv i (by simp)
      simp only [lowRaw0,lowRaw1] at hvi
      rw [hdt,haf.gpr,lowConstantsAt_frame haf,hda,hvi.1,hvi.2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFinal` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Round

def allLow : List LowIndex := (List.finRange 2).flatMap fun p => (List.finRange 4).map fun j => (p,j)
def finalLowCode (g : Nat) : List Instr := finalLoads++finalArithmetic++lowRunCode g allLow

def finalLowData (g : Nat) (s : State) : CheckData :=
  lowRun g (rawPairAt s) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) allLow

theorem lowReady_arithmetic {g : Nat} {s t : State} (h : LowReady g s)
    (hf : VChg stageRunRegs s t) : LowReady g t :=
  h.frame ((StepFrame.ofChg hf).mono (by intro r hr; exact List.mem_append_left _ hr))

theorem lowConstantsAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : lowConstantsAt t=lowConstantsAt s :=
  lowConstantsAt_frame ((StepFrame.ofChg hf).mono (by intro r hr; exact List.mem_append_left _ hr))

theorem finalLow_ok {g : Nat} (hg : IsG g) {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382)) (hc : LowReady g s)
    (hw : ∀i:LowIndex,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i+128)) 16)
    (k : ∀t,StepFrame lowRunRegs s t → dataAt t=finalLowData g s →
      WP isa (.block rest) t Q) : WP isa (.block (finalLowCode g++rest)) s Q := by
  simp only [finalLowCode,List.append_assoc]
  refine finalLoadArithmetic_ok hr ht hs hc.q fun a ha va => ?_
  refine lowRun_ok hg allLow (by decide) (va.lowPending allLow) (lowReady_arithmetic hc ha) ?_ fun t hf hd => ?_
  · simpa only [ha.rd,ha.wr,ha.gpr] using hw
  · refine k t (((StepFrame.ofChg ha).trans hf).mono (by simp [lowRunRegs])) ?_
    unfold finalLowData rawPairAt
    simpa only [ha.gpr,lowConstantsAt_arithmetic ha,dataAt_arithmetic ha] using hd

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPartition` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired (r0Pair finalPaired)

theorem allLow_flatMap (f : Nat → Nat → List Instr) :
    [0,1].flatMap (fun p => (List.range 4).flatMap (fun j => f p j))=
      allLow.flatMap (fun i => f i.1.val i.2.val) := by
  have he : ([0,1].flatMap fun p => (List.range 4).map fun j => (p,j))=
      allLow.map (fun i => (i.1.val,i.2.val)) := by decide
  have h := congrArg (fun xs : List (Nat × Nat) => xs.flatMap (fun i => f i.1 i.2)) he
  simpa only [List.flatMap_assoc,List.flatMap_map] using h

theorem lowRunCode_eq (g : Nat) :
    [0,1].flatMap (fun p => (List.range 4).flatMap (fun j => r0Pair g p j))=lowRunCode g allLow := by
  rw [allLow_flatMap]
  simp only [r0Pair_blocks,lowRunCode,lowRaw0,lowRaw1,lowOff]

theorem final_r0_eq (g : Nat) : finalPaired g=finalLowCode g++finalAdvance := by
  unfold finalPaired finalLowCode
  rw [finalPrefix_eq,lowRunCode_eq]
  simp only [List.append_assoc]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowMemory` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowRun_frame (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) {W : List Region} {ro ra : Region} {m : Mem}
    (ho : ro∈W) (ha : ra∈W)
    (hco : ∀i:LowIndex,ro.Contains (out+BitVec.ofNat 64 (lowOff i)) 16 ∧
      ro.Contains (out+BitVec.ofNat 64 (lowOff i+128)) 16)
    (hca : ∀i:LowIndex,ra.Contains (aux+BitVec.ofNat 64 (lowOff i)) 16 ∧
      ra.Contains (aux+BitVec.ofNat 64 (lowOff i+128)) 16)
    (hf : Frame W m d.mem) : Frame W m (lowRun g v out aux c d is).mem := by
  induction is generalizing d with
  | nil => exact hf
  | cons i is ih =>
    simp only [lowRun]
    exact ih _ ((((hf.write ho _ (hco i).1).write ho _ (hco i).2).write ha _ (hca i).1).write ha _ (hca i).2)

def lowPassData (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) : Nat → CheckData
  | 0 => d
  | u+1 =>
    let prev := lowPassData g work out aux c d u
    let v := fun p => Inverse.rawFinalValues (readPair prev.mem (work+BitVec.ofNat 64 (16*u)) 128 p)
    lowRun g v (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c prev allLow

theorem lowPass_frame (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u : Nat} (hu : u≤8) :
    Frame [⟨out,2048⟩,⟨aux,2048⟩] d.mem (lowPassData g work out aux c d u).mem := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [lowPassData]
    refine lowRun_frame _ _ _ _ _ _ _ (ro:=⟨out,2048⟩) (ra:=⟨aux,2048⟩)
      (by simp) (by simp) ?_ ?_ (ih (by omega))
    · intro i
      constructor <;> rw [BitVec.add_assoc,← BitVec.ofNat_add] <;>
        exact Offset.contains_base out (by dsimp only [lowOff]; omega) (by dsimp only [lowOff]; omega)
    · intro i
      constructor <;> rw [BitVec.add_assoc,← BitVec.ofNat_add] <;>
        exact Offset.contains_base aux (by dsimp only [lowOff]; omega) (by dsimp only [lowOff]; omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRead` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowPair_read_other (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (a : Addr)
    (h0 : Mem.Sep a 16 out0 16) (h1 : Mem.Sep a 16 out1 16)
    (h2 : Mem.Sep a 16 aux0 16) (h3 : Mem.Sep a 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read a 16=d.mem.read a 16 := by
  simp only [lowPairStep]
  rw [Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide),
    Mem.read_write_sep h1 (by decide),Mem.read_write_sep h0 (by decide)]

theorem lowRun_read_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (a : Addr)
    (hs : ∀i∈is,Mem.Sep a 16 (out+BitVec.ofNat 64 (lowOff i)) 16 ∧
      Mem.Sep a 16 (out+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      Mem.Sep a 16 (aux+BitVec.ofNat 64 (lowOff i)) 16 ∧
      Mem.Sep a 16 (aux+BitVec.ofNat 64 (lowOff i+128)) 16) :
    (lowRun g v out aux c d is).mem.read a 16=d.mem.read a 16 := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [lowRun,ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))]
    have h := hs i (by simp)
    exact lowPair_read_other _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem lowRun_count (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) : (lowRun g v out aux c d is).count=d.count := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih => exact ih _

theorem lowPass_count (g : Nat) (work out aux : Addr) (c : LowConstants) (d : CheckData) (n : Nat) :
    (lowPassData g work out aux c d n).count=d.count := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lowPassData,lowRun_count,ih]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowWriteValues` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord)

private theorem read128_write_self (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.write a 16 v).read a 16=v := by
  simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m a 16 v (by decide)

def lowHighOutput (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) : BitVec 128 :=
  laneVector fun e => lowHighWord g (lowInputValues m out raw e)

def lowLowOutput (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) (c : LowConstants) : BitVec 128 :=
  laneVector fun e => reduceWord (lowInputValues m out raw e-
    lowHighWord g (lowInputValues m out raw e)*vword c.scale e)

theorem lowPair_mem (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem=
      (((d.mem.write out0 16 (lowHighOutput g d.mem out0 raw0)).write out1 16
        (lowHighOutput g d.mem out1 raw1)).write aux0 16
        (lowLowOutput g d.mem out0 raw0 c)).write aux1 16 (lowLowOutput g d.mem out1 raw1 c) := rfl

/-- The first high output survives all three subsequent stores. -/
theorem lowPair_read_high0 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData)
    (h1 : Mem.Sep out0 16 out1 16) (h2 : Mem.Sep out0 16 aux0 16) (h3 : Mem.Sep out0 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read out0 16=lowHighOutput g d.mem out0 raw0 := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide),
    Mem.read_write_sep h1 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_high1 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData)
    (h2 : Mem.Sep out1 16 aux0 16) (h3 : Mem.Sep out1 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read out1 16=lowHighOutput g d.mem out1 raw1 := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_low0 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (h3 : Mem.Sep aux0 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read aux0 16=lowLowOutput g d.mem out0 raw0 c := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_low1 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read aux1 16=lowLowOutput g d.mem out1 raw1 c := by
  rw [lowPair_mem]
  exact read128_write_self _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFlagValue` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def lowMask (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) (c : LowConstants) (e : Nat) : BitVec 32 :=
  normMask (reduceWord (lowInputValues m out raw e-
    lowHighWord g (lowInputValues m out raw e)*vword c.scale e)) (vword c.lower e) (vword c.width e)

/-- Both paired coefficient checks contribute to the rejection accumulator. -/
theorem lowPair_flag (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags e=
      (vword d.flags e ||| lowMask g d.mem out0 raw0 c e) ||| lowMask g d.mem out1 raw1 c e := by
  simp only [lowPairStep,lowMask,laneVector_word _ he]

theorem lowPair_flag_zero (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags e=0 ↔
      (vword d.flags e=0 ∧ lowMask g d.mem out0 raw0 c e=0) ∧ lowMask g d.mem out1 raw1 c e=0 := by
  rw [lowPair_flag _ _ _ _ _ _ _ _ _ he]
  exact BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)

theorem lowRun_flag_zero_initial (g : Nat) (v : Values) (out aux : Addr)
    (c : LowConstants) (d : CheckData) (is : List LowIndex) {e : Nat} (he : e<4)
    (hz : vword (lowRun g v out aux c d is).flags e=0) : vword d.flags e=0 := by
  induction is generalizing d with
  | nil => exact hz
  | cons i is ih => exact ((lowPair_flag_zero _ _ _ _ _ _ _ _ _ he).mp (ih _ hz)).1.1

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSlotLayout` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowAddr (base : Addr) (i : LowIndex) (half : Fin 2) : Addr :=
  base+BitVec.ofNat 64 (lowOff i+128*half.val)

theorem lowAddr_sep (base : Addr) {i j : LowIndex} {h k : Fin 2}
    (hne : i≠j ∨ h≠k) : Mem.Sep (lowAddr base i h) 16 (lowAddr base j k) 16 := by
  have hi : i.1.val≠j.1.val ∨ i.2.val≠j.2.val ∨ h.val≠k.val := by
    by_contra hn
    simp only [not_or,not_not] at hn
    have he : i=j := Prod.ext (Fin.ext hn.1) (Fin.ext hn.2.1)
    have hh : h=k := Fin.ext hn.2.2
    rcases hne with hn | hn
    · exact hn he
    · exact hn hh
  simp only [lowAddr,lowOff]
  exact Offset.sep base (by omega) (by omega) (by omega)

theorem lowAddr_contains (base : Addr) {u : Nat} (hu : u<8) (i : LowIndex) (h : Fin 2) :
    (⟨base,2048⟩ : Region).Contains (lowAddr (base+BitVec.ofNat 64 (16*u)) i h) 16 := by
  simp only [lowAddr,lowOff,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base base (by omega) (by omega)

/-- Disjoint later paired checks preserve either half of either output. -/
theorem lowRun_read_slot_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hn : i∉is) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr out i h) 16=d.mem.read (lowAddr out i h) 16 := by
  apply lowRun_read_other
  intro j hj
  have hnij : i≠j := by intro he; subst j; exact hn hj
  have ho0 := lowAddr_sep (h:=h) (k:=0) out (Or.inl hnij)
  have ho1 := lowAddr_sep (h:=h) (k:=1) out (Or.inl hnij)
  have contain (base : Addr) (i : LowIndex) (h : Fin 2) :
      (⟨base,2048⟩ : Region).Contains (lowAddr base i h) 16 := by
    simp only [lowAddr,lowOff]
    exact Offset.contains_base base (by omega) (by omega)
  have ha0 := hd.sep (contain out i h) (contain aux j 0)
  have ha1 := hd.sep (contain out i h) (contain aux j 1)
  simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    And.intro ho0 (And.intro ho1 (And.intro ha0 ha1))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowInputFrame` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowAddr_contains_base (base : Addr) (i : LowIndex) (h : Fin 2) :
    (⟨base,2048⟩ : Region).Contains (lowAddr base i h) 16 := by
  simp only [lowAddr,lowOff]
  exact Offset.contains_base base (by omega) (by omega)

/-- Both original input vectors of a later pair survive this pair's four stores. -/
theorem lowPair_other_input (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) {i j : LowIndex} (hne : j≠i) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr out j h) 16=d.mem.read (lowAddr out j h) 16 := by
  apply lowPair_read_other
  · simpa only [lowAddr,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using
      lowAddr_sep (h:=h) (k:=0) out (Or.inl hne)
  · simpa only [lowAddr,Fin.val_one,Nat.mul_one] using
      lowAddr_sep (h:=h) (k:=1) out (Or.inl hne)
  · simpa only [lowAddr,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using
      hd.sep (lowAddr_contains_base out j h) (lowAddr_contains_base aux i 0)
  · simpa only [lowAddr,Fin.val_one,Nat.mul_one] using
      hd.sep (lowAddr_contains_base out j h) (lowAddr_contains_base aux i 1)

theorem lowMask_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128)
    (c : LowConstants) (e : Nat) (hm : m'.read out 16=m.read out 16) :
    lowMask g m' out raw c e=lowMask g m out raw c e := by
  simp only [lowMask,lowInputValues,hm]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowHalfOutput` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowHalfValue (v : Values) (i : LowIndex) (h : Fin 2) : BitVec 128 :=
  (v i.1)[2*i.2.val+h.val]

/-- Each half of a paired step writes its exact high result. -/
theorem lowPair_read_high (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr out i h) 16=lowHighOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) := by
  have hd0 (h : Fin 2) := hd.sep (lowAddr_contains_base out i h) (lowAddr_contains_base aux i 0)
  have hd1 (h : Fin 2) := hd.sep (lowAddr_contains_base out i h) (lowAddr_contains_base aux i 1)
  fin_cases h
  · exact lowPair_read_high0 _ _ _ _ _ _ _ _ _
      (lowAddr_sep out (h:=0) (k:=1) (Or.inr (by decide))) (hd0 0) (hd1 0)
  · exact lowPair_read_high1 _ _ _ _ _ _ _ _ _ (hd0 1) (hd1 1)

/-- Each half also writes its exact signed low result, including rejected paths. -/
theorem lowPair_read_low (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (i : LowIndex) (h : Fin 2) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr aux i h) 16=lowLowOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) c := by
  fin_cases h
  · exact lowPair_read_low0 _ _ _ _ _ _ _ _ _ (lowAddr_sep aux (h:=0) (k:=1) (Or.inr (by decide)))
  · exact lowPair_read_low1 _ _ _ _ _ _ _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPassRead` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowSlice_sep (base : Addr) {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u)
    (i j : LowIndex) (h t : Fin 2) :
    Mem.Sep (lowAddr (base+BitVec.ofNat 64 (16*k)) i h) 16
      (lowAddr (base+BitVec.ofNat 64 (16*u)) j t) 16 := by
  simp only [lowAddr,lowOff,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Earlier r0 iterations preserve both inputs of every later pair. -/
theorem lowPass_read_future (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u k : Nat} (hu : u≤k) (hk : k<8) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d u).mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16=
      d.mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16 := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_,ih (by omega)]
    intro j _
    have h0 := lowSlice_sep out (by omega : u<8) hk (by omega : k≠u) i j h 0
    have h1 := lowSlice_sep out (by omega : u<8) hk (by omega : k≠u) i j h 1
    have h2 := hd.sep (lowAddr_contains out hk i h) (lowAddr_contains aux (by omega : u<8) j 0)
    have h3 := hd.sep (lowAddr_contains out hk i h) (lowAddr_contains aux (by omega : u<8) j 1)
    simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
      And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRunFlags` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowPairAccept (g : Nat) (v : Values) (out : Addr) (c : LowConstants) (m : Mem)
    (e : Nat) (i : LowIndex) : Prop :=
  lowMask g m (out+BitVec.ofNat 64 (lowOff i)) (lowValue0 v i) c e=0 ∧
  lowMask g m (out+BitVec.ofNat 64 (lowOff i+128)) (lowValue1 v i) c e=0

/-- A paired r0 sequence accepts precisely all its original-input norm checks. -/
theorem lowRun_flag_zero_iff (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (hn : is.Nodup)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) {e : Nat} (he : e<4) :
    vword (lowRun g v out aux c d is).flags e=0 ↔
      vword d.flags e=0 ∧ ∀i∈is,lowPairAccept g v out c d.mem e i := by
  induction is generalizing d with
  | nil => simp only [lowRun,List.not_mem_nil,false_implies,implies_true,and_true]
  | cons i is ih =>
    have hn' := List.nodup_cons.mp hn
    rw [lowRun,ih _ hn'.2,lowPair_flag_zero _ _ _ _ _ _ _ _ _ he]
    have ht : (∀j∈is,lowPairAccept g v out c
        (lowPairStep g (lowValue0 v i) (lowValue1 v i)
          (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
          (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem e j) ↔
        ∀j∈is,lowPairAccept g v out c d.mem e j := by
      have hp (j : LowIndex) (hj : j∈is) : lowPairAccept g v out c
          (lowPairStep g (lowValue0 v i) (lowValue1 v i)
            (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
            (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem e j ↔
          lowPairAccept g v out c d.mem e j := by
        have hnij : j≠i := by intro h; subst j; exact hn'.1 hj
        have h0 := lowPair_other_input g v out aux c d hnij 0 hd
        have h1 := lowPair_other_input g v out aux c d hnij 1 hd
        simp only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at h0 h1
        unfold lowPairAccept
        rw [lowMask_read_eq _ _ _ _ _ h0,lowMask_read_eq _ _ _ _ _ h1]
      exact ⟨fun h j hj => (hp j hj).mp (h j hj),fun h j hj => (hp j hj).mpr (h j hj)⟩
    rw [ht]
    simp only [List.mem_cons,forall_eq_or_imp,lowPairAccept,and_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
