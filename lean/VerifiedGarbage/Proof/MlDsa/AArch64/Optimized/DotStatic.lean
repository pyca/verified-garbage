import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore

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
