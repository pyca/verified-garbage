module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
public import VerifiedGarbage.Proof.MlDsa.BoundedFourContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.BoundedFourContract
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Std.Tactic.BVDecide.Normalize.BitVec
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16

/-! ### `MlDsa.AArch64.Optimized.BoundedFourParseTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourScalarTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample (rbTry)

structure ScalarPairReady (η : Nat) (p : Addr) (L : List Zq) (b : Byte) (s : State) : Prop where
 consts : ScalarConsts η s
 bound : L.length≤256
 stored : Stored s.mem p L
 output : s.gpr .x3=coeffAddr p L.length
 remaining : (s.gpr .x4).toNat=256-L.length
 byte : s.gpr .x6=b.setWidth 64
 low : s.gpr .x7=BitVec.ofNat 64 (b.toNat%16)
 write : ∀j<256,InRegions s.wr (coeffAddr p j) 4

def ScalarRestPublic (s t : State) : Prop :=
 s.sp=t.sp ∧ s.gpr .x3=t.gpr .x3 ∧ (s.gpr .x4).toNat=(t.gpr .x4).toNat

theorem scalarRest_relCT {η : Nat} (hη : η=2∨η=4) :
    RelCT isa ScalarRestPublic
      (.ite (.zero .x .x4) (.block []) (.block (rbTry η))) (fun _ _=>True) := by
  have nilc : ∃h,(taint.check (Taint.ofRegs []) (.block ([] : List Instr)) h).isSome=true:=⟨_,by taint_decide⟩
  have tryc : ∃h,(taint.check (Taint.ofRegs [.x3]) (.block (rbTry η)) h).isSome=true := by
    rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩
  obtain ⟨_,hn⟩:=nilc
  obtain ⟨_,ht⟩:=tryc
  refine RelCT.ite (fun s t h=>by rw [eval_zero,eval_zero,eq_zero_iff,eq_zero_iff,h.2.2]) ?_ ?_
  · exact RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1.1 (fun _ hh=>False.elim (List.not_mem_nil hh))) hn
  · exact RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1.1 (fun r hr=>by
        rw [List.mem_singleton.mp hr]; exact h.1.2.1)) ht

theorem scalarLow_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq} {b : Byte}
    (h : ScalarPairReady η p L b s) (hl : L.length<256) :
    WP isa (.block (rbTry η++([.lsr .x .x7 .x6 4] : List Instr))) s fun t=>
      Keep scalarPairRegs s t ∧ t.gpr .x3=coeffAddr p (hbTry η L (b.toNat%16)).length ∧
      (t.gpr .x4).toNat=256-(hbTry η L (b.toNat%16)).length := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok hη
    (by omega_using []) h.consts h.low h.output h.remaining hl h.stored (h.write _ hl))
    fun a ⟨hk,_,h3,h4,_⟩=>?_
  refine WP.mono (scalarHigh_ok (s := a) (b := b)
    (by rw [hk.gpr .x6 (by decide)]; exact h.byte)) fun t ⟨ht,_⟩=>?_
  exact ⟨(hk.trans ht.keep).mono (by decide),by rw [ht.get .x3]; exact h3,
    by rw [ht.get .x4]; exact h4⟩

theorem scalarPair_relCT {η : Nat} (hη : η=2∨η=4) {p : Addr}
    {L M : List Zq} {b c : Byte} (hl : L.length=M.length) (hb : hbOks η b=hbOks η c) :
    RelCT isa (fun s t=>ScalarPairReady η p L b s ∧ ScalarPairReady η p M c t ∧ s.sp=t.sp)
      (scalarPair η) (fun _ _=>True) := by
  have hm : (hbTry η L (b.toNat%16)).length=(hbTry η M (c.toNat%16)).length := by
    rw [hbTry_length,hbTry_length,hl,show halfByteOk η (b.toNat%16)=halfByteOk η (c.toNat%16) from congrArg Prod.fst hb]
  have nilc : ∃h,(taint.check (Taint.ofRegs []) (.block ([] : List Instr)) h).isSome=true:=⟨_,by taint_decide⟩
  have lowc : ∃h,(taint.check (Taint.ofRegs [.x3])
      (.block (rbTry η++([.lsr .x .x7 .x6 4] : List Instr))) h).isSome=true := by
    rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩
  obtain ⟨_,hn⟩:=nilc
  obtain ⟨_,hc⟩:=lowc
  unfold scalarPair
  refine RelCT.ite (fun s t h=>by
    rw [remaining_zero h.1.remaining h.1.bound,remaining_zero h.2.1.remaining h.2.1.bound,hl]) ?_ ?_
  · exact RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1.2.2 (fun _ hh=>False.elim (List.not_mem_nil hh))) hn
  · refine RelCT.seq (R := ScalarRestPublic) ?_ (scalarRest_relCT hη)
    have ht := RelCT.taint (A := taint) _
      (fun s t (h : (ScalarPairReady η p L b s ∧ ScalarPairReady η p M c t ∧ s.sp=t.sp) ∧
          isa.eval (.zero .x .x4) s=some false)=>
        VG.Proof.MlKem.AArch64.agree_of h.1.2.2 (fun r hr=>by
          rw [List.mem_singleton.mp hr,h.1.1.output,h.1.2.1.output,hl])) hc
    intro s t a d u v h es et
    have he:=(ht _ _ _ _ _ _ h es et).1
    have hz:=h.2
    rw [remaining_zero h.1.1.remaining h.1.1.bound] at hz
    have hne : L.length≠256:=by simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
    have hlt : L.length<256:=by have:=h.1.1.bound; omega_using [hne, this]
    obtain ⟨_,_,ex,hu⟩:=scalarLow_ok hη h.1.1 hlt
    obtain ⟨_,_,ey,hv⟩:=scalarLow_ok hη h.1.2.1 (by rw [←hl]; exact hlt)
    obtain ⟨_,rfl⟩:=Exec.det es ex
    obtain ⟨_,rfl⟩:=Exec.det et ey
    exact ⟨he,by rw [hu.1.sp,hv.1.sp]; exact h.1.2.2,
      by rw [hu.2.1,hv.2.1,hm],by rw [hu.2.2,hv.2.2,hm]⟩

structure ScalarBodyReady (η : Nat) (p : Addr) (L : List Zq) (b : Byte) (s : State) : Prop where
 consts : ScalarConsts η s
 bound : L.length≤256
 stored : Stored s.mem p L
 output : s.gpr .x3=coeffAddr p L.length
 remaining : (s.gpr .x4).toNat=256-L.length
 byte : s.mem (s.gpr .x2)=b
 read : InRegions (s.rd++s.wr) (s.gpr .x2) 1
 write : ∀j<256,InRegions s.wr (coeffAddr p j) 4

theorem scalarLoad_ready {η : Nat} {p : Addr} {L : List Zq} {b : Byte} {s : State}
    (h : ScalarBodyReady η p L b s) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) s fun t=>
      t.sp=s.sp ∧ ScalarPairReady η p L b t := by
  refine WP.mono (scalarLoad_ok h.consts.x11 h.read) fun t ⟨hk,_,_,hb,hl⟩=>?_
  refine ⟨hk.sp,h.consts.keep hk.keep (by decide),h.bound,?_,?_,?_,?_,?_,?_⟩
  · rw [hk.mem]; exact h.stored
  · rw [hk.get .x3]; exact h.output
  · rw [hk.get .x4]; exact h.remaining
  · rw [hb,h.byte]
  · rw [hl,h.byte]
  · intro j hj; rw [hk.wr]; exact h.write j hj

theorem scalarBody_relCT {η : Nat} (hη : η=2∨η=4) {p : Addr}
    {L M : List Zq} {b c : Byte} (hl : L.length=M.length) (hb : hbOks η b=hbOks η c) :
    RelCT isa (fun s t=>ScalarBodyReady η p L b s ∧ ScalarBodyReady η p M c t ∧
        s.sp=t.sp ∧ s.gpr .x2=t.gpr .x2)
      (VG.Impl.MlDsa.AArch64.Sample.rbBody η) (fun _ _=>True) := by
  change RelCT isa _ (.seq (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) (scalarPair η)) _
  refine RelCT.seq (R := fun (s t : State)=>ScalarPairReady η p L b s ∧
    ScalarPairReady η p M c t ∧ s.sp=t.sp) ?_ (scalarPair_relCT hη hl hb)
  have hc : ∃h,(taint.check (Taint.ofRegs [.x2])
      (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) h).isSome=true:=⟨_,by taint_decide⟩
  obtain ⟨_,hc⟩:=hc
  have ht := RelCT.taint (A := taint) _
    (fun s t (h : ScalarBodyReady η p L b s ∧ ScalarBodyReady η p M c t ∧
        s.sp=t.sp ∧ s.gpr .x2=t.gpr .x2)=>
      VG.Proof.MlKem.AArch64.agree_of h.2.2.1 (fun r hr=>by
        rw [List.mem_singleton.mp hr]; exact h.2.2.2)) hc
  intro s t a d u v h es et
  have he:=(ht _ _ _ _ _ _ h es et).1
  obtain ⟨_,_,ex,hu⟩:=scalarLoad_ready h.1
  obtain ⟨_,_,ey,hv⟩:=scalarLoad_ready h.2.1
  obtain ⟨_,rfl⟩:=Exec.det es ex
  obtain ⟨_,rfl⟩:=Exec.det et ey
  exact ⟨he,hu.2,hv.2,by rw [hu.1,hv.1]; exact h.2.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourVectorTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourTaint`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorVal vectorBody)

/-- The only data-dependent address in the vector parser is indexed by its
four public rejection bits. Split before that lookup, so accepted values stay secret. -/
def vectorPrefix : List Instr :=
 ([.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6)] : List Instr)++
 (extractCode++acceptCode++maskCode)

def vectorSuffix (η : Nat) : List Instr :=
 ([.lsl .x .x6 .x6 6,.add .x .x13 .x12 .x6,
   .ldrq .v6 .x13 0,.ldr .x .x6 .x13 32] : List Instr)++
 (vectorVal η++([.vop (.tbl .v1 .v1 .v6),.strq .v1 .x3 0] : List Instr)++
 advanceCore++[.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs])

theorem vector_split (η : Nat) : vectorBody true η=vectorPrefix++vectorSuffix η := by
  rw [vectorBody_eq]
  simp only [vectorPrefix,vectorSuffix,selectCode,List.append_assoc,List.cons_append,List.nil_append]

theorem vectorPrefix_taint : ∃h,
    (taint.check (Taint.ofRegs [.x2]) (.block vectorPrefix) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem vectorSuffix_taint {η : Nat} (hη : η=2∨η=4) : ∃h,
    (taint.check (Taint.ofRegs [.x3,.x6,.x12]) (.block (vectorSuffix η)) h).isSome=true := by
  rcases hη with rfl|rfl
  · exact ⟨_,by taint_decide⟩
  · exact ⟨_,by taint_decide⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ## From `BoundedFourLeak.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- A table index depends on rejection decisions, not accepted coefficient values. -/
theorem accept_decide_congr {η a b : Nat} (hη : η=2∨η=4)
    (h : halfByteOk η a=halfByteOk η b) : decide (a<rbB η)=decide (b<rbB η) := by
  rw [halfByteOk_eq hη,halfByteOk_eq hη] at h
  by_cases ha : a<rbB η <;> by_cases hb : b<rbB η <;> simp_all <;> omega_using [ha, hb]

def bytePairMask (η : Nat) (a b : Byte) : Nat :=
 nibbleMask η (a.toNat%16) (a.toNat/16) (b.toNat%16) (b.toNat/16)

theorem bytePairMask_congr {η : Nat} (hη : η=2∨η=4) {a b c d : Byte}
    (ha : hbOks η a=hbOks η c) (hb : hbOks η b=hbOks η d) :
    bytePairMask η a b=bytePairMask η c d := by
  have ha0:=accept_decide_congr hη (congrArg Prod.fst ha)
  have ha1:=accept_decide_congr hη (congrArg Prod.snd ha)
  have hb0:=accept_decide_congr hη (congrArg Prod.fst hb)
  have hb1:=accept_decide_congr hη (congrArg Prod.snd hb)
  unfold bytePairMask nibbleMask
  rw [ha0,ha1,hb0,hb1]

/-- Both vector and scalar cursors depend only on the original transcript. -/
theorem transcript_prefix_length {η : Nat} {X Y : List Byte} {L M : List Zq}
    (h : X.map (hbOks η)=Y.map (hbOks η)) (hl : L.length=M.length) (j : Nat) :
    (rbFold η L (X.take j)).length=(rbFold η M (Y.take j)).length :=
  rbFold_length_congr hl (by rw [List.map_take,List.map_take,h])

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourVectorTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem sourceMask_loaded {η : Nat} {s a : State}
    (hv : a.v .v0=loadedVector s.mem (s.gpr .x2)) :
    sourceMask η a=bytePairMask η (s.mem (s.gpr .x2)) (s.mem (s.gpr .x2+1)) := by
  have h:=loadedVector_nibbles s.mem (s.gpr .x2)
  simp only [List.range,List.range.loop,List.map_cons,List.map_nil,nibbles,
    List.cons.injEq] at h
  simp only [sourceMask,sourceNibble,hv,bytePairMask]
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2.1]

theorem vectorPrefix_ok {η : Nat} (hη : η=2∨η=4) {s : State} {table : Addr}
    (hC : Consts η table s) (hi : InRegions (s.rd++s.wr) (s.gpr .x2) 4) :
    WP isa (.block vectorPrefix) s fun t=>
      Keep [.x6,.x7] s t ∧ t.mem=s.mem ∧
      t.gpr .x6=BitVec.ofNat 64
        (bytePairMask η (s.mem (s.gpr .x2)) (s.mem (s.gpr .x2+1))) := by
  unfold vectorPrefix
  rw [WP.block_append_iff]
  refine WP.mono (loadDup_ok s hi) fun a ⟨hk,hm,hv,ho⟩=>?_
  refine WP.mono (nibbleMask_ok hη a
    (by rw [ho .v23 (by decide)]; exact hC.nibble)
    (by rw [ho .v25 (by decide)]; exact hC.expand)
    (fun e he=>by rw [ho .v22 (by decide)]; exact hC.bound e he)
    (fun e he=>by rw [ho .v24 (by decide)]; exact hC.weights e he)
    (by rw [hk.gpr .x11 (by decide)]; exact hC.mask))
    fun t ⟨ht,htm,ht6,_,_⟩=>?_
  exact ⟨(hk.trans ht).mono (by decide),htm.trans hm,
    by rw [ht6,sourceMask_loaded hv]⟩

/-- The parser's relational entry condition reveals only the two bytes' rejection
bits, together with the address/cursor values already determined by prior bits. -/
structure VectorPublic (η : Nat) (s t : State) : Prop where
 left : Consts η (s.gpr .x12) s
 right : Consts η (t.gpr .x12) t
 readLeft : InRegions (s.rd++s.wr) (s.gpr .x2) 4
 readRight : InRegions (t.rd++t.wr) (t.gpr .x2) 4
 sp : s.sp=t.sp
 regs : ∀r∈[Reg.x2,.x3,.x12],s.gpr r=t.gpr r
 low : hbOks η (s.mem (s.gpr .x2))=hbOks η (t.mem (t.gpr .x2))
 high : hbOks η (s.mem (s.gpr .x2+1))=hbOks η (t.mem (t.gpr .x2+1))

def SuffixPublic (s t : State) : Prop :=
 s.sp=t.sp ∧ ∀r∈[Reg.x3,.x6,.x12],s.gpr r=t.gpr r

theorem vectorPrefix_relCT {η : Nat} (hη : η=2∨η=4) :
    RelCT isa (VectorPublic η) (.block vectorPrefix) SuffixPublic := by
  obtain ⟨_,hc⟩:=vectorPrefix_taint
  have ht : RelCT isa (VectorPublic η) (.block vectorPrefix) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun s t h=>
      VG.Proof.MlKem.AArch64.agree_of h.sp (fun r hr=>by
        rw [List.mem_singleton.mp hr]; exact h.regs .x2 (by decide))) hc
  intro s t tr sr a b h es et
  have he:=(ht _ _ _ _ _ _ h es et).1
  obtain ⟨_,_,ex,ha⟩:=vectorPrefix_ok hη h.left h.readLeft
  obtain ⟨_,_,ey,hb⟩:=vectorPrefix_ok hη h.right h.readRight
  obtain ⟨_,rfl⟩:=Exec.det es ex
  obtain ⟨_,rfl⟩:=Exec.det et ey
  refine ⟨he,?_,?_⟩
  · rw [ha.1.sp,hb.1.sp]; exact h.sp
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · rw [ha.1.gpr .x3 (by decide),hb.1.gpr .x3 (by decide)]
      exact h.regs .x3 (by decide)
    · rw [ha.2.2,hb.2.2,bytePairMask_congr hη h.low h.high]
    · rw [ha.1.gpr .x12 (by decide),hb.1.gpr .x12 (by decide)]
      exact h.regs .x12 (by decide)

theorem vectorBody_relCT {η : Nat} (hη : η=2∨η=4) :
    RelCT isa (VectorPublic η) (.block (vectorBody true η)) (fun _ _=>True) := by
  obtain ⟨_,hc⟩:=vectorSuffix_taint hη
  rw [vector_split]
  apply RelCT.block_append
  exact RelCT.seq (vectorPrefix_relCT hη)
    (RelCT.taint (A := taint) _ (fun _ _ h=>
      VG.Proof.MlKem.AArch64.agree_of h.1 h.2) hc)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourParseSetup`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorSetup)

def parseSetup : Nat→List Instr := fun η=>scalarSetup η++vectorSetup η++
 [.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs]

theorem parseSetup_inv {s : State} {η : Nat} (he : η=2∨η=4) {table p q : Addr}
    {L : List Zq} {X : List Byte} (hl : L.length≤256) (hx : X.length=272)
    (hT : TableAt s.mem table) (hS : Stored s.mem p L)
    (h2 : s.gpr .x2=q) (h3 : s.gpr .x3=p) (h4 : s.gpr .x4=BitVec.ofNat 64 (256-L.length))
    (ht : s.gpr .x19+6000=table) :
    WP isa (.block (parseSetup η)) s fun t=>
      Keep (.x0::parserRegs) s t ∧ t.mem=s.mem ∧ LoopInv t η table p q L X 0 t := by
  unfold parseSetup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (scalarSetup_ok he hl h3 h4) fun a ⟨ha,haC⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (vectorSetup_ok he haC.q haC.eta haC.mask haC.bound) fun b ⟨hb,hbC⟩=>?_
  have hbT : a.gpr .x19+6000=table := by rw [ha.keep.gpr .x19 (by decide)]; exact ht
  rw [hbT] at hbC
  refine WP.mono (guard_ok hbC.four hbC.zero) fun c ⟨hc,hcv,h8⟩=>?_
  have hk := (ha.keep.trans hb.keep).trans hc.keep
  have hm : c.mem=s.mem := hc.mem.trans (hb.mem.trans ha.mem)
  have hC : Consts η table c := hbC.keep hc.keep (by decide) (fun _ _=>congrFun hcv _)
  have hr : c.gpr .x4=BitVec.ofNat 64 (256-L.length) := by
    rw [hk.gpr .x4 (by decide)]; exact h4
  have hb5 : b.gpr .x5=272 := by rw [hb.keep.gpr .x5 (by decide)]; exact haC.bytes
  have hg : c.gpr .x8=if L.length≤252 then BitVec.ofNat 64 X.length else 0 := by
    rw [h8,hb5,hb.keep.gpr .x4 (by decide),ha.keep.gpr .x4 (by decide),h4,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using []),hx]
    by_cases hh : L.length≤252
    · rw [ite_eq_left hh,ite_eq_left (by omega_using [hh] : 4≤256-L.length)]
      rfl
    · rw [ite_eq_right hh,ite_eq_right (by omega_using [hh] : ¬4≤256-L.length)]
  have hi : LoopInv c η table p q L X 0 c := by
    refine ⟨by omega_using [],rfl,hC,?_,Keep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_,?_⟩
    · rw [hm]; exact hT
    · change Stored c.mem p L
      rw [hm]; exact hS
    · change c.gpr .x2=q+0#64
      rw [BitVec.add_zero]
      rw [hk.gpr .x2 (by decide)]; exact h2
    · change c.gpr .x3=coeffAddr p L.length
      rw [hc.get .x3,hb.keep.gpr .x3 (by decide)]; exact haC.output
    · exact hr
    · simp only [Nat.sub_zero,hx]
      rw [hc.get .x5]; exact hb5
    · exact hg
  exact ⟨hk.mono (by decide),hm,hi⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ## From `BoundedFourParseTrace.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def parseModel (η : Nat) : Prog isa :=
 .seq (.block parseAddress)
   (.seq (parseCore η) (.block VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parseNext))

/-- Reassociation and splitting a straight-line prefix preserve the exact trace. -/
theorem parse_exec_model {η : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η) s tr t) :
    Exec isa (parseModel η) s tr t := by
  change Exec isa (.seq (.block (parseAddress++parseSetup η))
    (.seq (.ite (.zero .x .x8) (.block []) (.loop (.block (vectorBody true η)) (.nonzero .x .x8)))
      (.seq (.block fallbackSetup)
        (.seq (.ite (.zero .x .x8) (.block []) (.loop (scalarLoopBody η) (.nonzero .x .x8)))
          (.block VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parseNext))))) s tr t at h
  cases h with | seq hp hr =>
    cases hr with | seq hv hr =>
      cases hr with | seq hf hr =>
        cases hr with | seq hs ht =>
          rw [Exec.block_iff,execBlock_append] at hp
          obtain ⟨⟨a,ta⟩,ha,hb⟩:=Option.bind_eq_some_iff.mp hp
          obtain ⟨⟨b,tb⟩,hc,he⟩:=Option.map_eq_some_iff.mp hb
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl,rfl⟩:=he
          have hx : Exec isa (parseModel η) s _ t :=
            .seq (.block ha) (.seq (.seq (.block hc) (.seq hv (.seq hf hs))) ht)
          simpa only [List.append_assoc] using hx

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

structure TranscriptPair (σ τ : State) (η : Nat) (table p q : Addr)
    (L M : List Zq) (X Y : List Byte) : Prop where
 left : Layout σ table p q X
 right : Layout τ table p q Y
 sp : σ.sp=τ.sp
 length : L.length=M.length
 bytes : X.map (hbOks η)=Y.map (hbOks η)

theorem TranscriptPair.bytes_length {σ τ : State} {η : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y) :
    X.length=Y.length := by
  simpa only [List.length_map] using congrArg List.length h.bytes

theorem TranscriptPair.parsed_length {σ τ : State} {η : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y) (d : Nat) :
    (parsed η L X d).length=(parsed η M Y d).length :=
  transcript_prefix_length h.bytes h.length d

theorem TranscriptPair.byte {σ τ : State} {η : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y)
    {i : Nat} (hi : i<X.length) : hbOks η X[i]! =hbOks η Y[i]! := by
  have hy : i<Y.length:=by rw [←h.bytes_length]; exact hi
  have hh:=congrArg (fun Z : List (Nat×Nat)=>Z[i]!) h.bytes
  simpa only [getElem!_pos (X.map (hbOks η)) i (by simpa using hi),
    getElem!_pos (Y.map (hbOks η)) i (by simpa using hy),List.getElem_map,
    getElem!_pos X i hi,getElem!_pos Y i hy] using hh

theorem loopInv_public {σ τ s t : State} {η d : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y)
    (hs : LoopInv σ η table p q L X d s) (ht : LoopInv τ η table p q M Y d t)
    (hd : d+2≤X.length) : VectorPublic η s t := by
  have hdY : d+2≤Y.length:=by rw [←h.bytes_length]; exact hd
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hs.consts.table]; exact hs.consts
  · rw [ht.consts.table]; exact ht.consts
  · rw [hs.keep.rd,hs.keep.wr,hs.input]; exact h.left.read d hd
  · rw [ht.keep.rd,ht.keep.wr,ht.input]; exact h.right.read d hdY
  · rw [hs.keep.sp,ht.keep.sp]; exact h.sp
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · rw [hs.input,ht.input]
    · rw [hs.output,ht.output,h.parsed_length]
    · rw [hs.consts.table,ht.consts.table]
  · rw [hs.input,ht.input,hs.stream h.left (by omega_arith),ht.stream h.right (by omega_arith)]
    exact h.byte (by omega_arith)
  · have ea : q+BitVec.ofNat 64 d+1=q+BitVec.ofNat 64 (d+1) := by
      rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
    rw [hs.input,ht.input,ea,hs.stream h.left (by omega_arith),ht.stream h.right (by omega_arith)]
    exact h.byte (by omega_arith)

theorem vectorLoopStep_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y) (hd : d+2≤X.length)
    (hl : (parsed η L X d).length≤252) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.block (vectorBody true η))
      (fun s t=>LoopInv σ η table p q L X (d+2) s ∧ LoopInv τ η table p q M Y (d+2) t) := by
  have hc:=RelCT.mono (vectorBody_relCT hη)
    (fun s t (hh : LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)=>
      loopInv_public h hh.1 hh.2 hd) (fun _ _ _=>True.intro)
  exact (hc.wp (fun s t hh=>
    ⟨vectorLoopStep_ok hη h.left hh.1 hd hl,
     vectorLoopStep_ok hη h.right hh.2 (by rw [←h.bytes_length]; exact hd)
       (by rw [←h.parsed_length]; exact hl)⟩)).mono
         (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

def VectorPairDone (σ τ : State) (η : Nat) (table p q : Addr)
    (L M : List Zq) (X Y : List Byte) (s t : State) : Prop :=
 ∃d,LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t ∧
   (d=X.length ∨ 252<(parsed η L X d).length)

theorem vectorLoop_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y) (hd : d<X.length)
    (hl : (parsed η L X d).length≤252) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.loop (.block (vectorBody true η)) (.nonzero .x .x8))
      (VectorPairDone σ τ η table p q L M X Y) := by
  let I := fun rank s t=>∃j,rank=X.length-j ∧
    LoopInv σ η table p q L X j s ∧ LoopInv τ η table p q M Y j t ∧
    j<X.length ∧ (parsed η L X j).length≤252
  have step (rank : Nat) : RelCT isa (I rank) (.block (vectorBody true η))
      (fun s t=>isa.eval (.nonzero .x .x8) s=isa.eval (.nonzero .x .x8) t ∧
        (isa.eval (.nonzero .x .x8) s=some false→VectorPairDone σ τ η table p q L M X Y s t) ∧
        (isa.eval (.nonzero .x .x8) s=some true→∃m<rank,I m s t)) := by
    intro s t a b u v hp es et
    obtain ⟨j,rfl,hs,ht,hj,hL⟩:=hp
    have hj2 : j+2≤X.length:=by have:=h.left.even; have:=hs.even; omega_arith
    obtain ⟨he,hu,hv⟩:=vectorLoopStep_relCT hη h hj2 hL _ _ _ _ _ _ ⟨hs,ht⟩ es et
    have eu:=loopGuard_eval h.left hu
    have ev:=loopGuard_eval h.right hv
    have ee : isa.eval (.nonzero .x .x8) u=isa.eval (.nonzero .x .x8) v := by
      rw [eu,ev,h.bytes_length,h.parsed_length]
    refine ⟨he,ee,?_,?_⟩
    · intro hz
      rw [eu] at hz
      have hn : ¬(j+2<X.length ∧ (parsed η L X (j+2)).length≤252) := by
        simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
      exact ⟨j+2,hu,hv,by have:=hu.bound; omega_arith⟩
    · intro hn
      rw [eu] at hn
      have hc : j+2<X.length ∧ (parsed η L X (j+2)).length≤252 := by
        simpa only [Option.some.injEq,decide_eq_true_eq] using hn
      exact ⟨X.length-(j+2),by omega_arith,j+2,rfl,hu,hv,hc⟩
  exact (RelCT.loop I step (X.length-d)).mono
    (fun _ _ hh=>⟨d,rfl,hh.1,hh.2,hd,hl⟩) (fun _ _ hh=>hh)

theorem vectorPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.ite (.zero .x .x8) (.block [])
        (.loop (.block (vectorBody true η)) (.nonzero .x .x8)))
      (VectorPairDone σ τ η table p q L M X Y) := by
  refine RelCT.ite (fun s t hh=>by
    rw [loopGuard_zero h.left hh.1,loopGuard_zero h.right hh.2,
      h.bytes_length,h.parsed_length]) ?_ ?_
  · intro s t a b u v hh es et
    have he : s=u ∧ a=[] := by
      cases es with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    have hf : t=v ∧ b=[] := by
      cases et with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    obtain ⟨rfl,rfl⟩:=he
    obtain ⟨rfl,rfl⟩:=hf
    have hz:=hh.2
    rw [loopGuard_zero h.left hh.1.1] at hz
    exact ⟨rfl,d,hh.1.1,hh.1.2,by
      simpa only [Option.some.injEq,decide_eq_true_eq] using hz⟩
  · intro s t a b u v hh es et
    have hz:=hh.2
    rw [loopGuard_zero h.left hh.1.1] at hz
    have hn : ¬(d=X.length ∨ 252<(parsed η L X d).length) := by
      simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
    have hd : d<X.length:=by have:=hh.1.1.bound; omega_arith
    exact vectorLoop_relCT hη h hd (by omega_arith) _ _ _ _ _ _ hh.1 es et

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

theorem ScalarInv.ready {σ s : State} {η d : Nat} {p q : Addr} {L : List Zq} {X : List Byte}
    (h : ScalarInv σ η p q L X d s) (hy : ScalarLayout σ p q X) (hl : L.length≤256)
    (hd : d<X.length) : ScalarBodyReady η p (parsed η L X d) X[d]! s := by
  refine ⟨h.consts,parsed_bound hl d,h.stored,h.output,h.remaining,?_,?_,?_⟩
  · rw [h.input,h.stream hy hd]
  · rw [h.keep.rd,h.keep.wr,h.input]; exact hy.read d hd
  · intro j hj; rw [h.keep.wr]; exact hy.write j hj

theorem scalarStep_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y)
    (hl : L.length≤256) (hd : d<X.length) :
    RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (scalarLoopBody η)
      (fun s t=>ScalarInv σ η p q L X (d+1) s ∧ ScalarInv τ η p q M Y (d+1) t) := by
  have hm : M.length≤256:=by rw [←h.length]; exact hl
  have hdy : d<Y.length:=by rw [←h.bytes_length]; exact hd
  have cb := (scalarBody_relCT hη (h.parsed_length d) (h.byte hd)).mono
    (fun s t (hh : ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)=>
      ⟨hh.1.ready sx hl hd,hh.2.ready sy hm hdy,
        by rw [hh.1.keep.sp,hh.2.keep.sp]; exact h.sp,
        by rw [hh.1.input,hh.2.input]⟩) (fun _ _ _=>True.intro)
  have cs : RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (VG.Impl.MlDsa.AArch64.Sample.rbBody η) (fun s t=>s.sp=t.sp) := by
    apply RelCT.mono (cb.wp (F₁ := fun (s : State)=>s.sp=σ.sp) (F₂ := fun (t : State)=>t.sp=τ.sp) ?_)
      (fun _ _ hh=>hh) (fun _ _ hh=>by rw [hh.2.1,hh.2.2]; exact h.sp)
    intro s t hh
    have a:=hh.1.ready sx hl hd
    have b:=hh.2.ready sy hm hdy
    exact ⟨WP.mono (scalarBody_ok hη a.consts a.bound a.stored a.output a.remaining a.read a.write)
      (fun _ ht=>ht.keep.sp.trans hh.1.keep.sp),
      WP.mono (scalarBody_ok hη b.consts b.bound b.stored b.output b.remaining b.read b.write)
      (fun _ ht=>ht.keep.sp.trans hh.2.keep.sp)⟩
  have cg : RelCT isa (fun (s t : State)=>s.sp=t.sp)
      (.block [.mul .x .x8 .x4 .x5]) (fun _ _=>True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of hh
        (fun _ hr=>False.elim (List.not_mem_nil hr))) (by taint_decide)
  exact ((RelCT.seq cs cg).wp (fun _ _ hh=>
    ⟨scalarStep_ok hη hl sx hh.1 hd,scalarStep_ok hη hm sy hh.2 hdy⟩)).mono
      (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

def ScalarPairDone (σ τ : State) (η : Nat) (p q : Addr)
    (L M : List Zq) (X Y : List Byte) (s t : State) : Prop :=
 ∃d,ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t ∧
   (d=X.length ∨ (parsed η L X d).length=256)

theorem scalarLoop_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y)
    (hL0 : L.length≤256) (hd : d<X.length)
    (hl : (parsed η L X d).length<256) :
    RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (.loop (scalarLoopBody η) (.nonzero .x .x8))
      (ScalarPairDone σ τ η p q L M X Y) := by
  let I := fun rank s t=>∃j,rank=X.length-j ∧
    ScalarInv σ η p q L X j s ∧ ScalarInv τ η p q M Y j t ∧
    j<X.length ∧ (parsed η L X j).length<256
  have step (rank : Nat) : RelCT isa (I rank) (scalarLoopBody η)
      (fun s t=>isa.eval (.nonzero .x .x8) s=isa.eval (.nonzero .x .x8) t ∧
        (isa.eval (.nonzero .x .x8) s=some false→ScalarPairDone σ τ η p q L M X Y s t) ∧
        (isa.eval (.nonzero .x .x8) s=some true→∃m<rank,I m s t)) := by
    intro s t a b u v hp es et
    obtain ⟨j,rfl,hs,ht,hj,hL⟩:=hp
    obtain ⟨he,hu,hv⟩:=scalarStep_relCT hη h sx sy hL0 hj _ _ _ _ _ _ ⟨hs,ht⟩ es et
    have eu:=scalarGuard_nonzero hL0 sx hu
    have ev:=scalarGuard_nonzero (by rw [←h.length]; exact hL0) sy hv
    have ee : isa.eval (.nonzero .x .x8) u=isa.eval (.nonzero .x .x8) v := by
      rw [eu,ev,h.bytes_length,h.parsed_length]
    refine ⟨he,ee,?_,?_⟩
    · intro hz
      rw [eu] at hz
      have hn : ¬(j+1<X.length ∧ (parsed η L X (j+1)).length<256) := by
        simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
      exact ⟨j+1,hu,hv,by have:=hu.bound; have:=parsed_bound (η := η) (X := X) hL0 (j+1); omega_arith⟩
    · intro hn
      rw [eu] at hn
      have hc : j+1<X.length ∧ (parsed η L X (j+1)).length<256 := by
        simpa only [Option.some.injEq,decide_eq_true_eq] using hn
      exact ⟨X.length-(j+1),by omega_arith,j+1,rfl,hu,hv,hc⟩
  exact (RelCT.loop I step (X.length-d)).mono
    (fun _ _ hh=>⟨d,rfl,hh.1,hh.2,hd,hl⟩) (fun _ _ hh=>hh)

theorem scalarPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y)
    (hL0 : L.length≤256) :
    RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (.ite (.zero .x .x8) (.block [])
        (.loop (scalarLoopBody η) (.nonzero .x .x8)))
      (ScalarPairDone σ τ η p q L M X Y) := by
  refine RelCT.ite (fun s t hh=>by
    rw [scalarGuard_zero hL0 sx hh.1,scalarGuard_zero (by rw [←h.length]; exact hL0) sy hh.2,
      h.bytes_length,h.parsed_length]) ?_ ?_
  · intro s t a b u v hh es et
    have he : s=u ∧ a=[] := by
      cases es with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    have hf : t=v ∧ b=[] := by
      cases et with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    obtain ⟨rfl,rfl⟩:=he
    obtain ⟨rfl,rfl⟩:=hf
    have hz:=hh.2
    rw [scalarGuard_zero hL0 sx hh.1.1] at hz
    exact ⟨rfl,d,hh.1.1,hh.1.2,by
      simpa only [Option.some.injEq,decide_eq_true_eq] using hz⟩
  · intro s t a b u v hh es et
    have hz:=hh.2
    rw [scalarGuard_zero hL0 sx hh.1.1] at hz
    have hn : ¬(d=X.length ∨ (parsed η L X d).length=256) := by
      simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
    have hd : d<X.length:=by have:=hh.1.1.bound; omega_arith
    exact scalarLoop_relCT hη h sx sy hL0 hd (by have:=parsed_bound (η := η) (X := X) hL0 d; omega_arith) _ _ _ _ _ _ hh.1 es et

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourParserTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem fallback_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y) (hL : L.length≤256) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (fallback η) (ScalarPairDone σ τ η p q L M X Y) := by
  unfold fallback
  refine RelCT.seq (R := fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
    ?_ (scalarPhase_relCT hη h sx sy hL)
  have hc : ∃hint,(taint.check (Taint.ofRegs []) (.block fallbackSetup) hint).isSome=true:=⟨_,by taint_decide⟩
  obtain ⟨_,hc⟩:=hc
  have ct : RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.block fallbackSetup) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [hh.1.keep.sp,hh.2.keep.sp]; exact h.sp)
      (fun _ hr=>False.elim (List.not_mem_nil hr))) hc
  exact (ct.wp (fun _ _ hh=>⟨fallbackSetup_inv hh.1,fallbackSetup_inv hh.2⟩)).mono
    (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

/-- All vector lookups, scalar stores, and both adaptive parser exits are
fixed by the standard bounded-sampler rejection transcript. -/
theorem parsedPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y) (hL : L.length≤256) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.seq (.ite (.zero .x .x8) (.block [])
        (.loop (.block (vectorBody true η)) (.nonzero .x .x8))) (fallback η))
      (ScalarPairDone σ τ η p q L M X Y) := by
  refine RelCT.seq (vectorPhase_relCT hη h) ?_
  apply RelCT.mono (RelCT.exists_ (fun j=>fallback_relCT (d := j) hη h sx sy hL))
  · intro s t hh
    obtain ⟨j,hs,ht,_⟩:=hh
    exact ⟨j,hs,ht⟩
  · intro _ _ hh; exact hh

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourCoreTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure CoreReady (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte) (s : State) : Prop where
 bound : L.length≤256
 bytes : X.length=272
 vectorLayout : Layout s table p q X
 scalarLayout : ScalarLayout s p q X
 tableMem : TableAt s.mem table
 stored : Stored s.mem p L
 input : s.gpr .x2=q
 output : s.gpr .x3=p
 count : s.gpr .x4=BitVec.ofNat 64 (256-L.length)
 tableAddr : s.gpr .x19+6000=table

theorem parseSetup_taint {η : Nat} (hη : η=2∨η=4) : ∃hint,
    (taint.check (Taint.ofRegs []) (.block (parseSetup η)) hint).isSome=true :=
  by rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseCore_relCT {η : Nat} (hη : η=2∨η=4) {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (hl : L.length=M.length)
    (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>CoreReady η table p q L X s ∧ CoreReady η table p q M Y t ∧ s.sp=t.sp)
      (parseCore η) (fun _ _=>True) := by
  obtain ⟨_,hc⟩:=parseSetup_taint hη
  have cs : RelCT isa (fun s t=>s.sp=t.sp) (.block (parseSetup η)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of hh
      (fun _ hr=>False.elim (List.not_mem_nil hr))) hc
  intro s t tr ur u v h es et
  cases es with | seq es0 es1 =>
    cases et with | seq et0 et1 =>
      have he:=(cs _ _ _ _ _ _ h.2.2 es0 et0).1
      obtain ⟨_,_,ex,ha⟩:=parseSetup_inv hη h.1.bound h.1.bytes h.1.tableMem h.1.stored
        h.1.input h.1.output h.1.count h.1.tableAddr
      obtain ⟨_,_,ey,hb⟩:=parseSetup_inv hη h.2.1.bound h.2.1.bytes h.2.1.tableMem h.2.1.stored
        h.2.1.input h.2.1.output h.2.1.count h.2.1.tableAddr
      obtain ⟨_,rfl⟩:=Exec.det es0 ex
      obtain ⟨_,rfl⟩:=Exec.det et0 ey
      have hp : TranscriptPair _ _ η table p q L M X Y :=
        ⟨h.1.vectorLayout.keep ha.1 ha.2.1,h.2.1.vectorLayout.keep hb.1 hb.2.1,
          by rw [ha.1.sp,hb.1.sp]; exact h.2.2,hl,hx⟩
      have ht:=(parsedPhase_relCT hη hp
        (h.1.scalarLayout.keep ha.1 ha.2.1) (h.2.1.scalarLayout.keep hb.1 hb.2.1)
        h.1.bound _ _ _ _ _ _ ⟨ha.2.2,hb.2.2⟩ es1 et1).1
      exact ⟨by rw [he,ht],trivial⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourParseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure ParseReady (table p q a : Addr) (L : List Zq) (X : List Byte) (s : State) : Prop where
 bound : L.length≤256
 bytes : X.length=272
 vectorLayout : Layout s table p q X
 scalarLayout : ScalarLayout s p q X
 tableMem : TableAt s.mem table
 stored : Stored s.mem p L
 input : s.gpr .x24=q
 output : s.gpr .x25=p
 countAddr : s.gpr .x26=a
 tableAddr : s.gpr .x19+6000=table
 count : s.mem.readW a 64=BitVec.ofNat 64 (256-L.length)
 read : InRegions (s.rd++s.wr) a 8

theorem parseAddress_ready {η : Nat}
    {table p q a : Addr} {L : List Zq} {X : List Byte} {s : State}
    (h : ParseReady table p q a L X s) :
    WP isa (.block parseAddress) s fun t=>
      VG.Proof.MlKem.AArch64.Only [.x2,.x3,.x4] s t ∧ CoreReady η table p q L X t := by
  refine WP.mono (parseAddress_ok (by rw [h.countAddr]; exact h.read)) fun t ⟨ht,h2,h3,h4⟩=>?_
  refine ⟨ht,h.bound,h.bytes,h.vectorLayout.keep ht.keep ht.mem,
    h.scalarLayout.keep ht.keep ht.mem,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.mem]; exact h.tableMem
  · rw [ht.mem]; exact h.stored
  · rw [h2]; exact h.input
  · rw [h3]; exact h.output
  · rw [h4,h.countAddr,h.count]
  · rw [ht.get .x19]; exact h.tableAddr

theorem parseAddress_taint : ∃h,
    (taint.check (Taint.ofRegs [.x26]) (.block parseAddress) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem parseNext_taint : ∃h,
    (taint.check (Taint.ofRegs [.x26])
      (.block VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parseNext) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem parseModel_relCT {η : Nat} (hη : η=2∨η=4)
    {table p q a : Addr} {L M : List Zq} {X Y : List Byte}
    (hl : L.length=M.length) (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>ParseReady table p q a L X s ∧ ParseReady table p q a M Y t ∧
      s.sp=t.sp)
      (parseModel η) (fun _ _=>True) := by
  obtain ⟨_,ha⟩:=parseAddress_taint
  obtain ⟨_,hz⟩:=parseNext_taint
  have ca : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x26=t.gpr .x26)
      (.block parseAddress) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2)) ha
  have cz : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x26=t.gpr .x26)
      (.block VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parseNext) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2)) hz
  intro s t tr ur u v h es et
  cases es with | seq es0 es1 =>
    cases es1 with | seq es1 es2 =>
      cases et with | seq et0 et1 =>
        cases et1 with | seq et1 et2 =>
          have h26 : s.gpr .x26=t.gpr .x26 := by rw [h.1.countAddr,h.2.1.countAddr]
          have e0:=(ca _ _ _ _ _ _ ⟨h.2.2,h26⟩ es0 et0).1
          obtain ⟨_,_,ex,sa⟩:=parseAddress_ready (η := η) h.1
          obtain ⟨_,_,ey,ta⟩:=parseAddress_ready (η := η) h.2.1
          obtain ⟨_,rfl⟩:=Exec.det es0 ex
          obtain ⟨_,rfl⟩:=Exec.det et0 ey
          have hs : _ := sa.2
          have ht : _ := ta.2
          have hsp : _ := sa.1.sp.trans (h.2.2.trans ta.1.sp.symm)
          have e1:=(parseCore_relCT hη hl hx _ _ _ _ _ _ ⟨hs,ht,hsp⟩ es1 et1).1
          obtain ⟨_,_,ex,hb⟩:=parseCore_ok hη hs.bound hs.bytes hs.vectorLayout hs.scalarLayout
            hs.tableMem hs.stored hs.input hs.output hs.count hs.tableAddr
          obtain ⟨_,_,ey,hc⟩:=parseCore_ok hη ht.bound ht.bytes ht.vectorLayout ht.scalarLayout
            ht.tableMem ht.stored ht.input ht.output ht.count ht.tableAddr
          obtain ⟨_,rfl⟩:=Exec.det es1 ex
          obtain ⟨_,rfl⟩:=Exec.det et1 ey
          have e2:=(cz _ _ _ _ _ _ ⟨by rw [hb.1.sp,hc.1.sp]; exact hsp,
            by rw [hb.1.gpr .x26 (by decide),hc.1.gpr .x26 (by decide),sa.1.get .x26,ta.1.get .x26]
               exact h26⟩ es2 et2).1
          exact ⟨by rw [e0,e1,e2],trivial⟩

theorem parse_relCT {η : Nat} (hη : η=2∨η=4)
    {table p q a : Addr} {L M : List Zq} {X Y : List Byte}
    (hl : L.length=M.length) (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>ParseReady table p q a L X s ∧ ParseReady table p q a M Y t ∧
      s.sp=t.sp)
      (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η) (fun _ _=>True) := by
  intro _ _ _ _ _ _ h es et
  exact parseModel_relCT hη hl hx _ _ _ _ _ _ h (parse_exec_model es) (parse_exec_model et)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourSmall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- Failure masking is per lane, so every output remains a small polynomial
regardless of the aggregate four-lane return value. -/
theorem Result.small {σ t : State} {η : Nat} (h : Result σ t (sampledRows σ η))
    {i : Nat} (hi : i<4) :
    ∃x : IPoly,polyAt t.mem (outputAt (samplerOut σ) i)=toRq x ∧
      VG.Proof.MlDsa.KeyGen.Small η x := by
  by_cases hf : (sampledRows σ η i).length=256
  · have hs := rejBounded_some η
      (ρ := Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) (B := 544)
      (by simpa only [sampledRows_H] using hf)
    obtain ⟨x,hx,he⟩:=Option.map_eq_some_iff.mp hs
    refine ⟨x,?_,VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    rw [h.full hi hf,sampledRows_H]
    exact he.symm
  · refine ⟨Vector.replicate 256 0,?_,VG.Proof.MlDsa.KeyGen.small_zero η⟩
    apply Vector.ext
    intro j hj
    simp only [polyAt,Vector.getElem_ofFn,h.words i hi j hj,resultWord,ite_eq_right hf,
      toRq,Vector.getElem_map,Vector.getElem_replicate]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourChunkLeak.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- The public transcript already determines each stream's rejection bits. -/
theorem fourLeak_stream {η : Nat} {σ τ : State}
    (h : rejBoundedFourLeak η σ.mem (samplerSeed σ)=
      rejBoundedFourLeak η τ.mem (samplerSeed τ)) {i : Nat} (hi : i<4) :
    rejBoundedLeak η (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66)=
      rejBoundedLeak η (Spec.Sha3.bytesAt τ.mem (samplerSeedAt τ i) 66) := by
  exact VG.Proof.MlDsa.KeyGen.flatMap_range_inj
    (fun _=>VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _)
    (fun _=>VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _) h i hi

/-- Splitting the original SHAKE rejection transcript adds no observable data. -/
theorem fourLeak_chunks {η : Nat} {σ τ : State}
    (h : rejBoundedFourLeak η σ.mem (samplerSeed σ)=
      rejBoundedFourLeak η τ.mem (samplerSeed τ)) {i : Nat} (hi : i<4) :
    (chunkBytes (samplerA σ i)).map (hbOks η)=
      (chunkBytes (samplerA τ i)).map (hbOks η) ∧
    (chunkBytes (Resident.permuted (samplerA σ i) 2)).map (hbOks η)=
      (chunkBytes (Resident.permuted (samplerA τ i) 2)).map (hbOks η) := by
  have he := leak_hbOks (fourLeak_stream h hi) (B := 544) (by decide)
  rw [←chunks_H,←chunks_H,List.map_append,List.map_append] at he
  exact List.append_inj he (by simp only [List.length_map,chunkBytes_length])

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

theorem BatchAt.parseReady {σ s : State} {b p : Addr} {η i off : Nat}
    {L : Nat→List Zq} {X : Nat→List Byte} (hi : i<4)
    (hy : BatchLayout σ b p off X) (h : BatchAt σ b p η off L X i s) :
    ParseReady (b+6000) (outputAt p i) (inputAt b i off) (countAt b i) (L i) (X i) s := by
  have hd : doneBatch η i L X i=L i := by simp [doneBatch]
  have hs := h.1
  have hb := hs.fields.bound i hi
  have hst := hs.fields.stored i hi
  have hc := hs.fields.count i hi
  rw [hd] at hb hst hc
  exact ⟨hb,hy.length i hi,
    (hy.vector i hi).frame hs.keep hs.frame (hy.streamsApart i hi),
    (hy.scalar i hi).frame hs.keep hs.frame (hy.streamsApart i hi),hs.table,hst,
    h.2.1,h.2.2.1,h.2.2.2.1,by rw [hs.base],hc,
    by rw [hs.keep.rd,hs.keep.wr]; exact hy.countRead i hi⟩

theorem batchAt_relCT {σ τ : State} {b p : Addr} {η i off : Nat}
    (hη : η=2∨η=4) (hi : i<4)
    {L M : Nat→List Zq} {X Y : Nat→List Byte}
    (sx : BatchLayout σ b p off X) (sy : BatchLayout τ b p off Y) (hsp : σ.sp=τ.sp)
    (hl : ∀j<4,(L j).length=(M j).length)
    (hx : ∀j<4,(X j).map (hbOks η)=(Y j).map (hbOks η)) :
    RelCT isa (fun s t=>BatchAt σ b p η off L X i s ∧ BatchAt τ b p η off M Y i t)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η)
      (fun s t=>BatchAt σ b p η off L X (i+1) s ∧ BatchAt τ b p η off M Y (i+1) t) := by
  have hc := (parse_relCT hη (hl i hi) (hx i hi)).mono
    (fun s t (h : BatchAt σ b p η off L X i s ∧ BatchAt τ b p η off M Y i t)=>
      ⟨h.1.parseReady hi sx,h.2.parseReady hi sy,
        by rw [h.1.1.keep.sp,h.2.1.keep.sp]; exact hsp⟩)
    (fun _ _ _=>True.intro)
  exact (hc.wp (fun _ _ h=>⟨batchAt_step hη hi sx h.1,batchAt_step hη hi sy h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

theorem batchInit_taint {off : Nat} (ho : off=0∨off=272) : ∃h,
    (taint.check (Taint.ofRegs [])
      (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.batchInit off)) h).isSome=true := by
  rcases ho with rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem batch_relCT {σ τ : State} {b p : Addr} {η off : Nat}
    (hη : η=2∨η=4) (ho : off=0∨off=272)
    {L M : Nat→List Zq} {X Y : Nat→List Byte}
    (sx : BatchLayout σ b p off X) (sy : BatchLayout τ b p off Y) (hsp : σ.sp=τ.sp)
    (hl : ∀j<4,(L j).length=(M j).length)
    (hx : ∀j<4,(X j).map (hbOks η)=(Y j).map (hbOks η)) :
    RelCT isa (fun s t=>BatchInv σ s b p L ∧ BatchInv τ t b p M)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off)
      (fun s t=>BatchInv σ s b p (fun i=>rbFold η (L i) (X i)) ∧
        BatchInv τ t b p (fun i=>rbFold η (M i) (Y i))) := by
  obtain ⟨_,hi⟩:=batchInit_taint ho
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.batch
  apply RelCT.seq (R := fun s t=>BatchAt σ b p η off L X 0 s ∧ BatchAt τ b p η off M Y 0 t)
  · have hc : RelCT isa (fun s t=>BatchInv σ s b p L ∧ BatchInv τ t b p M)
        (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.batchInit off)) (fun _ _=>True) :=
      RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
        (by rw [h.1.keep.sp,h.2.keep.sp]; exact hsp) (fun r hr=>by simp at hr)) hi
    exact (hc.wp (fun s t h=>⟨batchAt_init (by omega_using [ho]) h.1,batchAt_init (by omega_using [ho]) h.2⟩)).mono
      (fun _ _ h=>h) (fun _ _ h=>h.2)
  · refine (RelCT.loop (M := isa) (fun m s t=>∃ i,i<4 ∧ m=4-i ∧
        BatchAt σ b p η off L X i s ∧ BatchAt τ b p η off M Y i t)
      (fun m=>?_) 4).mono (fun s t h=>⟨0,by decide,rfl,h⟩) (fun _ _ h=>h)
    apply RelCT.exists_
    intro i
    intro s t tr ur s' t' ⟨hi,hm,h⟩ es et
    obtain ⟨htr,h1,h2⟩ := batchAt_relCT hη hi sx sy hsp hl hx s t tr ur s' t' h es et
    refine ⟨htr,?_,?_,?_⟩
    · rw [batchAt_eval h1,batchAt_eval h2]
    · intro he
      rw [batchAt_eval h1] at he
      have hl4 : i+1=4 := by simp at he; omega_using [hi, he]
      rw [hl4] at h1 h2
      exact ⟨h1.last,h2.last⟩
    · intro he
      rw [batchAt_eval h1] at he
      have hl4 : i+1<4 := by simp at he; omega_using [he]
      exact ⟨4-(i+1),by omega_using [hi, hm],i+1,hl4,rfl,h1,h2⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourRoundTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (squeezeTwo batch)

structure SamplerBases (σ τ : State) : Prop where
 scratch : samplerScratch σ=samplerScratch τ
 output : samplerOut σ=samplerOut τ
 sp : σ.sp=τ.sp

theorem sampleRound_relCT (sha3 : Bool) {η off : Nat} (hη : η=2∨η=4) (ho : off=0∨off=272)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq}
    (hl : ∀i<4,(L i).length=(M i).length)
    (hx : ∀i<4,(chunkBytes (A i)).map (hbOks η)=(chunkBytes (B i)).map (hbOks η)) :
    RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.seq (squeezeTwo sha3 off) (batch true η off))
      (fun s t=>SamplerRun σ s (fun i=>Resident.permuted (A i) 2)
        (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        SamplerRun τ t (fun i=>Resident.permuted (B i) 2)
        (fun i=>rbFold η (M i) (chunkBytes (B i)))) := by
  obtain ⟨_,hc⟩:=squeezeTwo_taint sha3 ho
  have cs : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19)
      (squeezeTwo sha3 off) (fun _ _=>True) :=
    VectorTaint.relRegs [.x19] (fun _ _ h=>⟨h.1,fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2⟩) hc
  have ct : RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.seq (squeezeTwo sha3 off) (batch true η off)) (fun _ _=>True) := by
    intro s t tr ur u v h es et
    cases es with | seq es0 es1 =>
      cases et with | seq et0 et1 =>
        have e0:=(cs _ _ _ _ _ _ ⟨by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp,
          by rw [h.1.env.x19,h.2.env.x19]; exact hb.scratch⟩ es0 et0).1
        obtain ⟨_,_,ex,ha⟩:=squeezeStage_ok sha3 hp h.1 (by omega_using [ho] : off≤272)
        obtain ⟨_,_,ey,hd⟩:=squeezeStage_ok sha3 hq h.2 (by omega_using [ho] : off≤272)
        obtain ⟨_,rfl⟩:=Exec.det es0 ex
        obtain ⟨_,rfl⟩:=Exec.det et0 ey
        have lx : BatchLayout _ (samplerScratch σ) (samplerOut σ) off (fun i=>chunkBytes (A i)) :=
          samplerBatchLayout_ok hp ha.1.env.wr (by omega_using [ho]) (fun _ _=>chunkBytes_length _)
            (fun i hi j hj=>by rw [chunkBytes_get _ hj]; exact stream136_byte (ha.2 i hi) (by omega_using [hj]))
        have ly : BatchLayout _ (samplerScratch τ) (samplerOut τ) off (fun i=>chunkBytes (B i)) :=
          samplerBatchLayout_ok hq hd.1.env.wr (by omega_using [ho]) (fun _ _=>chunkBytes_length _)
            (fun i hi j hj=>by rw [chunkBytes_get _ hj]; exact stream136_byte (hd.2 i hi) (by omega_using [hj]))
        have ia : BatchInv _ _ (samplerScratch σ) (samplerOut σ) L :=
          ⟨VG.Proof.MlKem.AArch64.Keep.refl _ _,Frame.refl _ _,ha.1.env.x19,ha.1.env.x21,ha.1.table,ha.1.fields⟩
        have ib : BatchInv _ _ (samplerScratch τ) (samplerOut τ) M :=
          ⟨VG.Proof.MlKem.AArch64.Keep.refl _ _,Frame.refl _ _,hd.1.env.x19,hd.1.env.x21,hd.1.table,hd.1.fields⟩
        rw [←hb.scratch,←hb.output] at ly ib
        have e1:=(batch_relCT hη ho lx ly
          (by rw [ha.1.env.sp,hd.1.env.sp]; exact hb.sp) hl hx _ _ _ _ _ _ ⟨ia,ib⟩ es1 et1).1
        exact ⟨by rw [e0,e1],trivial⟩
  exact (ct.wp (fun _ _ h=>⟨sampleRound_ok sha3 hη hp h.1 (by omega_using [ho]),
      sampleRound_ok sha3 hη hq h.2 (by omega_using [ho])⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourAdaptiveTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure FlaggedPair (σ τ s t : State) (A B : Nat→Spec.Sha3.State) (L M : Nat→List Zq) : Prop where
 left : SamplerRun σ s A L
 right : SamplerRun τ t B M
 leftFlag : s.gpr .x27=countFlag L
 rightFlag : t.gpr .x27=countFlag M

theorem countFlag_length {L M : Nat→List Zq} (h : ∀i<4,(L i).length=(M i).length) :
    countFlag L=countFlag M := by
  unfold countFlag foldedFlags
  change ((BitVec.ofNat 64 (256-(L 0).length)|||BitVec.ofNat 64 (256-(L 1).length))|||
    BitVec.ofNat 64 (256-(L 2).length))|||BitVec.ofNat 64 (256-(L 3).length)=_
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]
  rfl

theorem flagsStage_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq} :
    RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags)
      (fun s t=>FlaggedPair σ τ s t A B L M) := by
  obtain ⟨_,hc⟩:=flags_taint
  have ct : RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp) (fun r hr=>by
        rw [List.mem_singleton.mp hr,h.1.env.x19,h.2.env.x19]; exact hb.scratch)) hc
  exact (ct.wp (fun _ _ h=>⟨flagsStage_ok hp h.1,flagsStage_ok hq h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>⟨h.2.1.1,h.2.2.1,h.2.1.2,h.2.2.2⟩)

theorem secondBatch_relCT (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq}
    (hl : ∀i<4,(L i).length=(M i).length)
    (hx : ∀i<4,(chunkBytes (A i)).map (hbOks η)=(chunkBytes (B i)).map (hbOks η)) :
    RelCT isa (fun s t=>FlaggedPair σ τ s t A B L M) (secondBatch sha3 η)
      (fun s t=>(∃A',SamplerRun σ s A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        s.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i)))) ∧
        (∃B',SamplerRun τ t B' (fun i=>rbFold η (M i) (chunkBytes (B i))) ∧
        t.gpr .x27=countFlag (fun i=>rbFold η (M i) (chunkBytes (B i))))) := by
  have ct : RelCT isa (fun s t=>FlaggedPair σ τ s t A B L M) (secondBatch sha3 η)
      (fun _ _=>True) := by
    unfold secondBatch
    refine RelCT.ite (fun s t h=>by
      rw [VG.Proof.MlKem.AArch64.eval_zero,VG.Proof.MlKem.AArch64.eval_zero,
        h.leftFlag,h.rightFlag,countFlag_length hl]) ?_ ?_
    · have hn : ∃hint,(taint.check (Taint.ofRegs []) (.block ([] : List Instr)) hint).isSome=true:=⟨_,by taint_decide⟩
      obtain ⟨_,hn⟩:=hn
      exact RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
        (by rw [h.1.left.env.sp,h.1.right.env.sp]; exact hb.sp)
        (fun _ hr=>False.elim (List.not_mem_nil hr))) hn
    · exact (RelCT.assoc (RelCT.seq (sampleRound_relCT sha3 hη (Or.inr rfl) hp hq hb hl hx)
        (flagsStage_relCT hp hq hb))).mono
          (fun _ _ h=>⟨h.1.left,h.1.right⟩) (fun _ _ _=>True.intro)
  exact (ct.wp (fun _ _ h=>⟨secondBatch_ok sha3 hη hp h.left h.leftFlag,
      secondBatch_ok sha3 hη hq h.right h.rightFlag⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourEndTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

theorem maskStage_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerBases σ τ) {L M : Nat→List Zq} :
    RelCT isa (fun s t=>(∃A,SamplerRun σ s A L ∧ s.gpr .x27=countFlag L) ∧
      (∃B,SamplerRun τ t B M ∧ t.gpr .x27=countFlag M)) maskFour
      (fun s t=>Sampled σ s L ∧ Sampled τ t M) := by
  obtain ⟨_,hc⟩:=maskFour_taint
  have ct : RelCT isa (fun s t=>(∃A,SamplerRun σ s A L ∧ s.gpr .x27=countFlag L) ∧
      (∃B,SamplerRun τ t B M ∧ t.gpr .x27=countFlag M)) maskFour (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>by
      obtain ⟨⟨A,ha,haf⟩,⟨B,hb',hbf⟩⟩:=h
      apply VG.Proof.MlKem.AArch64.agree_of
      · rw [ha.env.sp,hb'.env.sp]; exact hb.sp
      · intro r hr
        rcases (show r=Reg.x19∨r=Reg.x21 by simpa using hr) with rfl|rfl
        · rw [ha.env.x19,hb'.env.x19]; exact hb.scratch
        · rw [ha.env.x21,hb'.env.x21]; exact hb.output) hc
  exact (ct.wp (fun _ _ h=>by
    obtain ⟨⟨A,ha,haf⟩,⟨B,hb',hbf⟩⟩:=h
    exact ⟨maskStage_ok hp ha haf,maskStage_ok hq hb' hbf⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

theorem finish_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerBases σ τ) {L M : Nat→List Zq} :
    RelCT isa (fun s t=>Sampled σ s L ∧ Sampled τ t M)
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        Impl.MlDsa.AArch64.Sample.Rej4.epi))
      (fun s t=>Result σ s L ∧ Result τ t M) := by
  obtain ⟨_,hc⟩:=finish_taint
  have ct : RelCT isa (fun s t=>Sampled σ s L ∧ Sampled τ t M)
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        Impl.MlDsa.AArch64.Sample.Rej4.epi)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp) (fun r hr=>by
        rw [List.mem_singleton.mp hr,h.1.env.x19,h.2.env.x19]; exact hb.scratch)) hc
  exact (ct.wp (fun _ _ h=>⟨finish_ok hp h.1,finish_ok hq h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure SamplerPublic (η : Nat) (σ τ : State) : Prop extends SamplerBases σ τ where
 seed : samplerSeed σ=samplerSeed τ
 leak : rejBoundedFourLeak η σ.mem (samplerSeed σ)=rejBoundedFourLeak η τ.mem (samplerSeed τ)

theorem setup_relCT {η : Nat} {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerPublic η σ τ) :
    RelCT isa (fun s t=>s=σ ∧ t=τ) (.block samplerSetup)
      (fun s t=>SamplerRun σ s (samplerA σ) (fun _=>[]) ∧
        SamplerRun τ t (samplerA τ) (fun _=>[])) := by
  obtain ⟨_,hc⟩:=samplerSetup_taint
  have ct : RelCT isa (fun s t=>s=σ ∧ t=τ) (.block samplerSetup) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>by
      rcases h with ⟨rfl,rfl⟩
      apply VG.Proof.MlKem.AArch64.agree_of hb.sp
      intro r hr
      rcases (show r=Reg.x0∨r=Reg.x1∨r=Reg.x2 by simpa using hr) with rfl|rfl|rfl
      · exact hb.seed
      · exact hb.output
      · exact hb.scratch) hc
  exact (ct.wp (F₁ := Ready σ) (F₂ := Ready τ) (fun _ _ h=>by
    rcases h with ⟨rfl,rfl⟩
    exact ⟨samplerSetup_ok hp,samplerSetup_ok hq⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>⟨h.2.1.running,h.2.2.running⟩)

/-- All data-dependent parsing and retry decisions are determined by the
original scalar rejection transcript; coefficient values remain secret. -/
theorem sampler_relCT (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerPublic η σ τ) :
    RelCT isa (fun s t=>s=σ ∧ t=τ)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (fun s t=>Result σ s (sampledRows σ η) ∧ Result τ t (sampledRows τ η)) := by
  have h0 := fun i hi=>(fourLeak_chunks hb.leak (i := i) hi).1
  have h1 := fun i hi=>(fourLeak_chunks hb.leak (i := i) hi).2
  have hl : ∀i<4,(rbFold η [] (chunkBytes (samplerA σ i))).length=
      (rbFold η [] (chunkBytes (samplerA τ i))).length := by
    intro i hi
    exact rbFold_length_congr rfl (h0 i hi)
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler
  change RelCT isa _ (.seq (.block samplerSetup) _) _
  apply RelCT.seq (setup_relCT hp hq hb)
  apply RelCT.assoc
  apply RelCT.seq (sampleRound_relCT sha3 hη (Or.inl rfl) hp hq hb.toSamplerBases
    (fun _ _=>rfl) h0)
  apply RelCT.seq (flagsStage_relCT hp hq hb.toSamplerBases)
  change RelCT isa _ (.seq (secondBatch sha3 η) _) _
  apply RelCT.seq (secondBatch_relCT sha3 hη hp hq hb.toSamplerBases hl h1)
  change RelCT isa _ (.seq maskFour _) _
  exact RelCT.seq (maskStage_relCT hp hq hb.toSamplerBases)
    (finish_relCT hp hq hb.toSamplerBases)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

def samplerK (η : Nat) : Contract isa where
 pre s := (η=2∨η=4) ∧ SamplerPre s
 post s t := (∀i<4,Reduced t.mem (samplerOut s+BitVec.ofNat 64 (1024*i))) ∧
   (∀i<4,BoundedOutput η t.mem (samplerOut s+BitVec.ofNat 64 (1024*i))) ∧
   Outcome (fun b=>(rejBoundedFour η b.rejBounded s.mem (samplerSeed s)).map (List.map toRq))
     ((t.gpr .x0).setWidth 32)
     ((List.range 4).map fun i=>polyAt t.mem (samplerOut s+BitVec.ofNat 64 (1024*i)))
 pub s t := SamplerPublic η s t

theorem sampler_correct (sha3 : Bool) (η : Nat) (s : State) (h : (samplerK η).pre s) :
    ∃tr t,Exec isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) s tr t ∧
      abiPreserved s t ∧ (samplerK η).post s t := by
  obtain ⟨tr,t,he,ht⟩:=sampler_machine_ok sha3 h.1 h.2
  exact ⟨tr,t,he,ht.abi,(fun i hi=>ht.reduced hi),(fun i hi=>ht.small hi),ht.outcome⟩

theorem sampler_ct (sha3 : Bool) (η : Nat) :
    ConstantTime isa (samplerK η).pre (samplerK η).pub
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) := by
  intro s t tr ur u v hs ht hp es et
  exact (sampler_relCT sha3 hs.1 hs.2 ht.2 hp s t tr ur u v ⟨rfl,rfl⟩ es et).1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

theorem sampler_pre (η : Nat) : ∀s,(rejBoundedFourContract abi η).pre s → (samplerK η).pre s := by
  intro s h
  sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at h
  sig_split h
  exact ⟨h,by assumption,by assumption,by assumption,by assumption,by assumption⟩

def samplerSat : State where
 gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 16384 else 0
 sp := 65536
 mem _ := 0
 rd := [⟨4096,264⟩]
 wr := [⟨8192,4096⟩,⟨16384,8192⟩]

theorem sampler_verified (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) :
    Verified target (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (rejBoundedFourContract abi η) := by
  refine Verified.of_correct (sampler_correct sha3 η) (sampler_ct sha3 η)
    { pre := sampler_pre η,post := ?_,pub := ?_,sat := ?_ }
  · sig_implies_post [rejBoundedFourContract,rejBoundedFourSig,samplerK,
      samplerOut,samplerSeed,ResidentRej.aP,ResidentRej.seedP,abi,argRegs]
  · intro s t _ _ h
    sig_pub [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at h
    obtain ⟨hsp,hl,h0,h1,h2⟩:=h
    exact ⟨⟨h2,h1,hsp⟩,h0,hl⟩
  · refine ⟨samplerSat,?_⟩
    sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
    sig_and_intros
    all_goals first | exact hη | rfl | exact Region.disjoint_of_sep (by decide) | decide

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
