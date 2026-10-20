module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingContext
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Combine machine correctness with the public-address timing checks -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

def Pair (g : Geometry) (rs : List Reg) (s t : State) : Prop :=
  Context g s ∧ Context g t ∧ VG.X86.Taint.Agree (timingTaint rs) s t

theorem timing_regs {s t : State} {rs : List Reg}
    (h : VG.X86.Taint.Agree (timingTaint rs) s t) {r : Reg} (hr : r ∈ rs) :
    s.gpr r = t.gpr r := h.rf.1 r (by simp only [timingTaint, RegSet.mem_ofList]; exact List.mem_cons_of_mem _ hr)

theorem timing_forget {s t : State} {rs : List Reg}
    (h : VG.X86.Taint.Agree (timingTaint rs) s t) : VG.X86.Taint.Agree (timingTaint []) s t := by
  refine timing_republish h ⟨?_, fun h => nomatch h⟩
  intro r hr
  simp only [timingTaint, RegSet.mem_ofList, List.mem_singleton] at hr
  subst r
  exact h.sp (by change 0 < 24; decide)

theorem timing_add_regs {s t : State} {rs : List Reg}
    (h : VG.X86.Taint.Agree (timingTaint []) s t)
    (regs : ∀ r ∈ rs, s.gpr r = t.gpr r) : VG.X86.Taint.Agree (timingTaint rs) s t := by
  refine timing_republish h ⟨?_, fun h => nomatch h⟩
  intro r hr
  simp only [timingTaint, RegSet.mem_ofList, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact h.sp (by change 0 < 24; decide)
  · exact regs r hr

theorem lift {g : Geometry} (v : g.Valid) {code : Prog isa} {before after : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (timingTaint before)) code
      (VG.X86.Taint.Agree (timingTaint [])))
    (F : State → State → Prop)
    (correct : ∀ s, Context g s → WP isa code s (F s))
    (keep : ∀ s t, F s t → Keeps clob7 s t)
    (writes : ∀ s t, F s t → Outs g.W g.writes s.mem t.mem)
    (publicRegs : ∀ s t u z, Pair g before s t → F s u → F t z →
      ∀ r ∈ after, u.gpr r = z.gpr r) :
    RelCT isa (Pair g before) code (Pair g after) := by
  intro s t tr ur u z H E G
  obtain ⟨sameTrace, A⟩ := raw _ _ _ _ _ _ H.2.2 E G
  have Fs := wp_result (correct s H.1) E
  have Ft := wp_result (correct t H.2.1) G
  exact ⟨sameTrace, H.1.keep v (keep s u Fs) (by decide) (writes s u Fs) A.wf₁,
    H.2.1.keep v (keep t z Ft) (by decide) (writes t z Ft) A.wf₂,
    timing_add_regs A (publicRegs s t u z H Fs Ft)⟩

theorem pair_regs {g : Geometry} {s t : State} {before after : List Reg}
    (H : Pair g before s t) (subset : ∀ r ∈ after, r ∈ before) : Pair g after s t :=
  ⟨H.1, H.2.1, timing_add_regs (timing_forget H.2.2) fun r hr => timing_regs H.2.2 (subset r hr)⟩

def WindowPair (g : Geometry) (w : Nat) (s t : State) : Prop :=
  Pair g [.ebp, .edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S ∧
    PtrAt s g.W .ebp w ∧ PtrAt t g.W .ebp w

theorem preserve_position {g : Geometry} {w : Nat} {code : Prog isa} {rs : List Reg}
    (raw : RelCT isa (WindowPair g w) code (Pair g [.ebp, .edi]))
    (correct : ∀ s, Context g s → PtrAt s g.W .edi g.S → PtrAt s g.W .ebp w →
      WP isa code s fun t => Keeps rs s t)
    (edi : .edi ∉ rs) (ebp : .ebp ∉ rs) :
    RelCT isa (WindowPair g w) code (WindowPair g w) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, P⟩ := raw _ _ _ _ _ _ H E G
  have Ku := wp_result (correct s H.1.1 H.2.1 H.2.2.2.1) E
  have Kz := wp_result (correct t H.1.2.1 H.2.2.1 H.2.2.2.2) G
  refine ⟨trace, P, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, Ku.1 .edi edi]; exact H.2.1
  · rw [PtrAt, Kz.1 .edi edi]; exact H.2.2.1
  · rw [PtrAt, Ku.1 .ebp ebp]; exact H.2.2.2.1
  · rw [PtrAt, Kz.1 .ebp ebp]; exact H.2.2.2.2

theorem lift_readonly {g : Geometry} (v : g.Valid) {code : Prog isa} {before after : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (timingTaint before)) code
      (VG.X86.Taint.Agree (timingTaint after)))
    (correct : ∀ s, WP isa code s fun t => t.mem = s.mem ∧ Keeps clob7 s t) :
    RelCT isa (Pair g before) code (Pair g after) := by
  intro s t tr ur u z H E G
  obtain ⟨sameTrace, A⟩ := raw _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, Ku⟩ := wp_result (correct s) E
  obtain ⟨Mz, Kz⟩ := wp_result (correct t) G
  refine ⟨sameTrace, H.1.keep v Ku (by decide) ?_ (timing_wf_regs A.wf₁),
    H.2.1.keep v Kz (by decide) ?_ (timing_wf_regs A.wf₂), A⟩
  · rw [Mu]; exact Outs.refl _ _ _
  · rw [Mz]; exact Outs.refl _ _ _

end VG.Proof.Mont.X86.Compact
