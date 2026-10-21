module

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.TimingColumns
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.TimingFinish
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingCore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Narrow
public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # Compose symmetric columns with the prepared reduction and restoration -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def SquarePair (g : Compact.Geometry) (s t : State) : Prop :=
  Compact.Context g s ∧ Compact.Context g t ∧
    (∃ A, ColumnReady s g.W g.L g.N g.S g.o g.a A) ∧
    (∃ B, ColumnReady t g.W g.L g.N g.S g.o g.a B) ∧ s.gpr .esp = t.gpr .esp

theorem columns_relCT {g : Compact.Geometry} (v : g.Valid) :
    RelCT isa (SquarePair g) VG.Impl.Mont.X86.PreparedSquare.columns
      (Compact.WindowPair g (g.S + VG.Impl.Mont.X86.Compact.accOff + 4 * g.N)) := by
  intro s t ls lt u z H ES ET
  obtain ⟨_, R⟩ := H.2.2.1
  obtain ⟨_, T⟩ := H.2.2.2.1
  exact columns_window_trace v H.1 H.2.1 R T H.2.2.2.2 ES ET

theorem inner_trace {g : Compact.Geometry} (v : g.Valid) :
    RelCT isa (SquarePair g)
      (.seq VG.Impl.Mont.X86.PreparedSquare.core (.block VG.Impl.Mont.X86.PreparedSquare.restore))
      (VG.X86.Taint.Agree (Compact.timingTaint [])) := by
  simp only [VG.Impl.Mont.X86.PreparedSquare.core, VG.Impl.Mont.X86.PreparedSquare.seqs]
  exact Compact.unassoc (RelCT.seq (columns_relCT v)
    (RelCT.seq (RelCT.seq (Compact.subM_relCT v) (finish_context_trace v)) (restore_trace v)))

end VG.Proof.Mont.X86.PreparedSquare
