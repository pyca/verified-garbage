import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSelect
import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTaint

/-! ## From `BoundedFourLeak.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- A table index depends on rejection decisions, not accepted coefficient values. -/
theorem accept_decide_congr {η a b : Nat} (hη : η=2∨η=4)
    (h : halfByteOk η a=halfByteOk η b) : decide (a<rbB η)=decide (b<rbB η) := by
  rw [halfByteOk_eq hη,halfByteOk_eq hη] at h
  by_cases ha : a<rbB η <;> by_cases hb : b<rbB η <;> simp_all <;> omega

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

/-- Equality of the old per-byte transcript determines each vector lookup. -/
theorem transcript_pair {η : Nat} (hη : η=2∨η=4) {X Y : List Byte}
    (h : X.map (hbOks η)=Y.map (hbOks η)) (j : Nat)
    (hx : j+1<X.length) (hy : j+1<Y.length) :
    bytePairMask η X[j]! X[j+1]! =bytePairMask η Y[j]! Y[j+1]! := by
  have hat (i : Nat) (hi : i<X.length) (hj : i<Y.length) :
      hbOks η X[i]! =hbOks η Y[i]! := by
    have hh:=congrArg (fun L : List (Nat×Nat)=>L[i]!) h
    simpa only [getElem!_pos (X.map (hbOks η)) i (by simpa using hi),
      getElem!_pos (Y.map (hbOks η)) i (by simpa using hj),List.getElem_map,
      getElem!_pos X i hi,getElem!_pos Y i hj] using hh
  exact bytePairMask_congr hη (hat j (by omega) (by omega)) (hat (j+1) hx hy)

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
