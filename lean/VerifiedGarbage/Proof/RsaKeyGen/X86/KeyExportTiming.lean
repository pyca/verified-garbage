module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportState
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyClearExport
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # All seven masked key outputs have a public address trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Impl.Mont.X86.Dynamic

structure ExportPair (E : Environment) (s t : State) : Prop where
  left : ExportState E s
  right : ExportState E t
  stack : s.gpr .esp = t.gpr .esp
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t

theorem ExportPair.output {E : Environment} {s t : State} (P : ExportPair E s t) : OutputPair E s t :=
  ⟨⟨P.left.input, P.right.input, P.stack⟩, P.agree, P.left.bit, P.right.bit⟩

theorem clearExport_trace (E : Environment) :
    RelCT isa (OutputPair E) (zerosW (VG.Impl.Rsa.X86.Keys.slot E.n aZero) (E.n + 2)) (ExportPair E) := by
  intro s t tr ur u v P A C
  have checked : KeyPublic (zerosW (VG.Impl.Rsa.X86.Keys.slot E.n aZero) (E.n + 2)) :=
    ⟨zerosHint true, zerosTaint true, zeros_check true _ _, rfl⟩
  obtain ⟨trace, agree⟩ := key_public_trace checked _ _ _ _ _ _ P.2.1 A C
  obtain ⟨leftState, leftKeeps⟩ := wp_result (clearExport_ok P.1.left P.2.2.1) A
  obtain ⟨rightState, rightKeeps⟩ := wp_result (clearExport_ok P.1.right P.2.2.2) C
  refine ⟨trace, leftState, rightState, ?_, agree⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.1.stack

theorem writePort_pair_trace (E : Environment) (i : Nat) (hi : i < 7) :
    RelCT isa (ExportPair E) (writePort E.n i) (ExportPair E) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := writePort_trace E i hi _ _ _ _ _ _ P.output A C
  obtain ⟨leftState, leftKeeps⟩ := wp_result (P.left.port_ok hi) A
  obtain ⟨rightState, rightKeeps⟩ := wp_result (P.right.port_ok hi) C
  refine ⟨trace, leftState, rightState, ?_, agree⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.stack

theorem writePorts_trace (E : Environment) (i count : Nat) (bound : i + count ≤ 7) :
    RelCT isa (ExportPair E) (writePorts E.n i count) (ExportPair E) := by
  induction count generalizing i with
  | zero => exact RelCT.block_nil (fun _ _ P => P)
  | succ count ih =>
    exact RelCT.seq (writePort_pair_trace E i (by omega)) (ih (i + 1) (by omega))

theorem writeOutputs_trace (E : Environment) :
    RelCT isa (OutputPair E) (writeOutputs E.n) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold writeOutputs seqs
  apply RelCT.seq (clearExport_trace E)
  apply RelCT.seq (writePorts_trace E 0 7 (by decide))
  have checked : KeyPublic (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kStatus))]) :=
    ⟨.block [], workspaceTaint true, rfl, rfl⟩
  exact (key_public_trace checked).mono (fun _ _ P => P.agree) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Key
