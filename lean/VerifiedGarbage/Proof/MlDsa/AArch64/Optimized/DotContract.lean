import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
import VerifiedGarbage.Spec.MlDsa.FusedInverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre

/-! ## From `DotStatic.lean` -/

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
  · intro off ho; exact ⟨_,htr,VG.Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,ha,VG.Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,hb,VG.Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,List.mem_append_right _ hw,VG.Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,hw,VG.Offset.contains_base _ ho (by omega)⟩
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

theorem dotNTT_eq_dotPoly (f g : Nat → Poly) (count : Nat) :
    dotNTT f g count=dotPoly f g count := rfl

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
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
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
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
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
    have hu : k/32<8 := by change k<256 at hk; omega
    have hi : (k%32)/4<8 := by omega
    have he : k%4<4 := by omega
    rw [dotPass_processed ha hb (by decide) hk hu,
      getElem!_pos (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count)) ((k%32)/4) hi]
    have hbank := bank (k/32) hu
    refine ⟨(hbank.1 ⟨(k%32)/4,hi⟩ _ he).1,(hbank.1 ⟨(k%32)/4,hi⟩ _ he).2,?_⟩
    have hv := hbank.2 ⟨(k%32)/4,hi⟩ _ he
    have hidx : 32*(k/32)+4*((k%32)/4)+k%4=k := by omega
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
  obtain ⟨hd,held,_,hsep,ht,hw,rest⟩ := h
  have hrd : s.rd=[dotFamilyRegion (s.gpr .x1) count,dotFamilyRegion (s.gpr .x2) count,
      tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    have he : count*256*4=1024*count := by omega
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
