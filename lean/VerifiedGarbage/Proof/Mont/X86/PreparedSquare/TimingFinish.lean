module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingSub
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingFinish
import VerifiedGarbage.Proof.Mont.X86.Compact.SelectAll
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare

/-! # Existing result reduction and scratch-register restoration compose -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

theorem finish_context_trace {g : Compact.Geometry} (v : g.Valid) :
    RelCT isa (Compact.BorrowPair g)
      (.seq (.block VG.Impl.Mont.X86.Rt.mask) VG.Impl.Mont.X86.Compact.select) (Compact.Pair g []) := by
  intro s t ls lt u z H ES ET
  obtain ⟨trace, Agree⟩ := Compact.finish_trace v _ _ _ _ _ _ H ES ET
  obtain ⟨cs, Cs⟩ := H.2.1
  obtain ⟨ct, Ct⟩ := H.2.2
  have acc : VG.Impl.Mont.X86.Compact.accOff = 24 := rfl
  have fit := v.lay.scr
  have out := v.outScratch
  obtain ⟨OS, _, KS⟩ := wp_result (Compact.selectAll_ok H.1.1.1.ws H.1.1.1.args v.base
    H.1.1.1.metadata.width (by have := v.lay.header; omega) v.outIndex H.1.1.1.outPtr
    v.positive v.n32 (by omega) v.outFit (by omega) H.1.2.2.2.1 Cs) ES
  obtain ⟨OT, _, KT⟩ := wp_result (Compact.selectAll_ok H.1.1.2.1.ws H.1.1.2.1.args v.base
    H.1.1.2.1.metadata.width (by have := v.lay.header; omega) v.outIndex H.1.1.2.1.outPtr
    v.positive v.n32 (by omega) v.outFit (by omega) H.1.2.2.2.2 Ct) ET
  have writes {m m' : Mem} (O : Outside g.W g.o (4 * g.N) m m') : Outs g.W g.writes m m' :=
    Outs.of_outside O (by change (g.o, 4 * g.N) ∈ [(g.S, 8 * g.N + 28), (g.o, 4 * g.N)]; simp)
  exact ⟨trace, H.1.1.1.keep v KS (by decide) (writes OS) (Compact.timing_wf_regs Agree.wf₁),
    H.1.1.2.1.keep v KT (by decide) (writes OT) (Compact.timing_wf_regs Agree.wf₂), Compact.timing_forget Agree⟩

theorem restore_tail_trace : RelCT isa (VG.X86.Taint.Agree (Compact.timingTaint [.edi]))
    (.block [.mov .ecx (.reg .edi), .mov .ebx (.mem (VG.Impl.Mont.X86.at_ .ecx 0)),
      .mov .esi (.mem (VG.Impl.Mont.X86.at_ .ecx 4)), .mov .ebp (.mem (VG.Impl.Mont.X86.at_ .ecx 8)),
      .mov .edi (.mem (VG.Impl.Mont.X86.at_ .ecx 12))])
    (VG.X86.Taint.Agree (Compact.timingTaint [])) :=
  erased_relCT _ _ (.block []) rfl rfl rfl rfl

theorem restore_trace {g : Compact.Geometry} (v : g.Valid) :
    RelCT isa (Compact.Pair g []) (.block VG.Impl.Mont.X86.PreparedSquare.restore)
      (VG.X86.Taint.Agree (Compact.timingTaint [])) := by
  unfold VG.Impl.Mont.X86.PreparedSquare.restore
  exact RelCT.block_append (RelCT.seq (Compact.scratchPointer_relCT v)
    (restore_tail_trace.mono (fun _ _ H => H.2.2) (fun _ _ H => H)))

end VG.Proof.Mont.X86.PreparedSquare
