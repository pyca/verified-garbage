import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductCore

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlKem.AArch64 (mov)

theorem multiplyInverseMem_frame (raw : Bool) (m : Mem) (p a b : Addr) :
    Frame [outputRegion p] m (multiplyInverseMem raw m p a b) := by
  apply (productPass_frame (m := m) (p := p) (a := a) (b := b) (u := 8) (by decide)).trans
  cases raw with
  | false => exact finalPass_frame (by decide)
  | true => exact rawFinalPass_frame (by decide)

theorem productCore_words_ok (raw : Bool) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (htr : tableRegion (s.gpr .x1)∈s.rd++s.wr)
    (har : polyRegion (s.gpr .x13)∈s.rd++s.wr)
    (hbr : polyRegion (s.gpr .x14)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x13)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x14)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.core raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) := by
  refine WP.mono (productCore_ok raw ht hsep ha hb ?_ ?_ ?_ ?_ ?_) fun t ⟨hk,hp,hm⟩ => ?_
  · intro off ho; exact ⟨_,htr,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,har,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,hbr,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,List.mem_append_right _ hw,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,hw,Offset.contains_base _ ho (by omega)⟩
  · exact ⟨hk,hp,by rw [hm]; exact multiplyInverseMem_frame _ _ _ _ _,hm⟩

theorem productStaticInit_ok (s : State) :
    WP isa (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) s fun t =>
      (t.gpr .x13=s.gpr .x1 ∧ t.gpr .x14=s.gpr .x2 ∧
        t.gpr .x1=s.syms "VG_MLDSA_INV_FOLDED" ∧ t.mem=s.mem) ∧ Keep [.x1,.x13,.x14] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold mov
  arun [exec_adrSym]
  rfl

theorem productStatic_words_ok (raw : Bool) {s : State}
    (ht : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED"))
    (htr : tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr)
    (har : polyRegion (s.gpr .x1)∈s.rd++s.wr)
    (hbr : polyRegion (s.gpr .x2)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x2)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode
  refine WP.seq (WP.mono (productStaticInit_ok s) fun a ⟨⟨h13,h14,h1,hm⟩,hk⟩ => ?_)
  have ht' : InverseTable.Words a.mem (a.gpr .x1) := by simpa only [h1,hm] using ht.words
  have h0 : a.gpr .x0=s.gpr .x0 := hk.get .x0 (by decide)
  refine WP.mono (productCore_words_ok raw ht' ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hpt,hft,hmt⟩ => ?_
  · simpa only [h1,hk.rd,hk.wr] using htr
  · simpa only [h13,hk.rd,hk.wr] using har
  · simpa only [h14,hk.rd,hk.wr] using hbr
  · simpa only [h0,hk.wr] using hw
  · simpa only [h1,h0] using hsep
  · simpa only [h13,h0] using ha
  · simpa only [h14,h0] using hb
  · exact ⟨(hk.trans hkt).mono,hpt.trans h0,
      by simpa only [hm,h0] using hft,
      by simpa only [hm,h0,h13,h14] using hmt⟩

theorem productCoreKeep_abi {s t : State} (h : Keep productCoreRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
