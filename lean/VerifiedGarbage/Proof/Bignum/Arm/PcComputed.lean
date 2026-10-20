module

public import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.ExportState
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! # The arithmetic result is ready for serialization to the caller's buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (wOf Layout)

structure PcComputed (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop where
  buffers : PcBuffers base dst src len k s
  stack : PcStack base dst src len k s
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = Spec.Rsa.modulusWords k
  ptr : s.gpr .r0 = base

theorem pcComputed_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcPrepared base dst src len k s) : WP isa precompute s (PcComputed base dst src len k) := by
  have countFit := (pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space).2.2.2.2
  refine WP.mono (precompute_ok s h.input.workspace h.input.layout h.input.width h.input.positive
    h.input.fits h.input.sourceFits h.input.readable h.input.separate h.input.ptr h.input.source h.input.count
    h.input.stackRead h.input.stackSep h.input.saved h.input.large h.input.odd countFit) ?_
  rintro t ⟨ready, _, _, frame, rest⟩
  exact ⟨h.buffers.congr rest, h.stack.after_workspace frame rest, ready.layout, ready.width, ready.ptr⟩

theorem pcExport_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcComputed base dst src len k s) :
    WP isa (.block [.ldrSp .r4 4]) s (ExportState base dst len (Spec.Rsa.modulusWords k) (16 * Spec.Rsa.modulusWords k)) := by
  refine WP.mono (pcOutput_ok s h.stack) ?_
  rintro t ⟨output, mem, rest⟩
  refine ⟨h.buffers.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr,
    output, by omega, h.buffers.outputFits, ?_, h.buffers.outputSeparate⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [rest.wr]; exact h.buffers.writable

end VG.Proof.Bignum.Arm
