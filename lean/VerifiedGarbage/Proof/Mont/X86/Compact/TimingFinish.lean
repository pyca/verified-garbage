module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingSub
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingCarry
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Mont.X86.Rt.Csub
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Conditional subtraction and selection keep the reduction decision secret -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

theorem mask_context_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (BorrowPair g) (.block Rt.mask) (WindowPair g (g.S + Compact.accOff + 8 * g.N)) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := mask_relCT _ _ _ _ _ _ H.1.1.2.2 E G
  obtain ⟨cs, Cs⟩ := H.2.1
  obtain ⟨ct, Ct⟩ := H.2.2
  have acc : Compact.accOff = 24 := rfl
  have fit := v.lay.scr
  obtain ⟨_, Mu, Ku⟩ := wp_result (mask_ok H.1.1.1.ws H.1.2.2.2.1 (by omega) Cs) E
  obtain ⟨_, Mz, Kz⟩ := wp_result (mask_ok H.1.1.2.1.ws H.1.2.2.2.2 (by omega) Ct) G
  refine ⟨trace, ⟨H.1.1.1.keep v Ku (by decide) ?_ (timing_wf_regs A.wf₁),
    H.1.1.2.1.keep v Kz (by decide) ?_ (timing_wf_regs A.wf₂), A⟩, ?_, ?_, ?_, ?_⟩
  · rw [Mu]; exact Outs.refl _ _ _
  · rw [Mz]; exact Outs.refl _ _ _
  · rw [PtrAt, Ku.1 .edi (by decide)]; exact H.1.2.1
  · rw [PtrAt, Kz.1 .edi (by decide)]; exact H.1.2.2.1
  · rw [PtrAt, Ku.1 .ebp (by decide)]; exact H.1.2.2.2.1
  · rw [PtrAt, Kz.1 .ebp (by decide)]; exact H.1.2.2.2.2

theorem select_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.ebp, .edi]) Compact.select
      (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .edi])) := by
  have header : 128 ≤ g.L := by have := v.lay.header; have := v.lay.scr; omega
  have output : RelCT isa (Pair g [.ebp, .edi]) (.block (Compact.operandPtr .esi 2 .edx)) (Pair g [.esi, .ebp]) :=
    (operandPointer_relCT v .esi .edx 2 ((g.W.toNat + g.o) % 2 ^ 32) outSelectPtr_relCT
      (by decide) (by decide) (by decide) (by intro _ _; have := v.outIndex; omega)
      (fun _ C => C.outPtr) (by decide) (by decide)).mono
      (fun _ _ H => pair_regs H (by decide)) (fun _ _ H => H)
  unfold Compact.select
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (length_relCT v .eax .edx 0 byteLength_relCT (by decide) (by decide))
    (RelCT.block_append (RelCT.seq (restorePointer_relCT v) (RelCT.block_append (RelCT.seq output
      (length_relCT v .edi .eax 0 outputLength_relCT (by decide) (by decide)))))))) ?_
  exact selectLoop_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem finish_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (BorrowPair g) (.seq (.block Rt.mask) Compact.select)
      (VG.X86.Taint.Agree (timingTaint [.ebp, .esi, .edi])) :=
  RelCT.seq (mask_context_relCT v) ((select_trace v).mono (fun _ _ H => H.1) (fun _ _ H => H))

end VG.Proof.Mont.X86.Compact
