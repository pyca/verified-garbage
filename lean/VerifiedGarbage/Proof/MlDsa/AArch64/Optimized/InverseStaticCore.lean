import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def tableRegion (p : Addr) : Region := ⟨p,3904⟩
def outputRegion (p : Addr) : Region := ⟨p,1024⟩

theorem inverseMem_frame (m : Mem) (p : Addr) : Frame [outputRegion p] m (inverseMem m p) :=
  (firstPass_frame (m := m) (p := p) (by decide)).trans (finalPass_frame (by decide))

theorem core_words_ok {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (htr : tableRegion (s.gpr .x1)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Inverse.core s fun t =>
      Keep coreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧ t.mem=inverseMem s.mem (s.gpr .x0) := by
  refine WP.mono (core_ok ht hsep ?_ ?_ ?_) fun t ⟨hk,hp,hm⟩ => ?_
  · intro off ho
    exact ⟨_,htr,VG.Offset.contains_base _ ho (by omega)⟩
  · intro off ho
    exact ⟨_,List.mem_append_right _ hw,VG.Offset.contains_base _ ho (by omega)⟩
  · intro off ho
    exact ⟨_,hw,VG.Offset.contains_base _ ho (by omega)⟩
  · exact ⟨hk,hp,by rw [hm]; exact inverseMem_frame _ _,hm⟩

theorem staticInit_ok (s : State) :
    WP isa (.block [.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_INV_FOLDED" ∧ t.mem=s.mem) ∧ Keep [.x1] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [exec_adrSym]

/-- Exact standalone inverse, using the registered immutable artifact and
writing only its in-place polynomial buffer. The scratch argument is unused. -/
theorem staticCode_words_ok {s : State}
    (ht : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED"))
    (htr : tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Inverse.staticCode s fun t =>
      Keep coreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧ t.mem=inverseMem s.mem (s.gpr .x0) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Inverse.staticCode
  refine WP.seq (WP.mono (staticInit_ok s) fun a ⟨⟨ha,hm⟩,hk⟩ => ?_)
  have ht' : InverseTable.Words a.mem (a.gpr .x1) := by simpa only [ha,hm] using ht.words
  refine WP.mono (core_words_ok ht' ?_ ?_ ?_) fun t ⟨hkt,hpt,hft,hmt⟩ => ?_
  · simpa only [ha,hk.rd,hk.wr] using htr
  · simpa only [hk.get .x0 (by decide),hk.wr] using hw
  · simpa only [ha,hk.get .x0 (by decide)] using hsep
  · exact ⟨(hk.trans hkt).mono,hpt.trans (hk.get .x0 (by decide)),
      by simpa only [hm,hk.get .x0 (by decide)] using hft,
      by simpa only [hm,hk.get .x0 (by decide)] using hmt⟩

theorem coreKeep_abi {s t : State} (h : Keep coreRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
