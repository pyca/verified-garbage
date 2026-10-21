module


public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Narrow
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.TimingArgs
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Columns
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.X86.Isa

/-! # Symmetric columns hand public pointers to the existing result reduction -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

theorem context_keep_columns {g : Compact.Geometry} {s t : State}
    (C : Compact.Context g s) (header : 128 ≤ g.S) (span : g.S + 8 * g.N + 32 ≤ g.L)
    (outIndex : (g.A 2).toNat < 8) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs)
    (O : Outside g.W g.S (8 * g.N + 32) s.mem t.mem) : Compact.Context g t := by
  refine ⟨C.ws.of_keeps K, C.args.of_keeps K sp ?_, C.metadata.keep O header, ?_,
    Compact.timing_wf_keeps C.wf K sp⟩
  · exact Outs.of_outside (O.mono (o' := 0) (n' := g.L) (by omega) (by omega)) (by simp)
  · rw [O.w32 (by omega) (by have := C.ws.nowrap; omega)]
    exact C.outPtr

theorem columns_window_trace {g : Compact.Geometry} (valid : g.Valid)
    {s t u v : State} {A B : Nat → BitVec 32}
    (CS : Compact.Context g s) (CT : Compact.Context g t)
    (R : ColumnReady s g.W g.L g.N g.S g.o g.a A)
    (T : ColumnReady t g.W g.L g.N g.S g.o g.a B)
    (sp : s.gpr .esp = t.gpr .esp) {ls lt : List Leak}
    (ES : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns s ls u)
    (ET : Exec isa VG.Impl.Mont.X86.PreparedSquare.columns t lt v) :
    ls = lt ∧ Compact.WindowPair g (g.S + VG.Impl.Mont.X86.Compact.accOff + 4 * g.N) u v := by
  have trace := columns_trace R T sp ES ET
  obtain ⟨OS, _, BS, _, _, KS⟩ := wp_result
    (columns_ok R.args R.ws R.values R.lay R.positive R.edi R.inverse R.small) ES
  obtain ⟨OT, _, BT, _, _, KT⟩ := wp_result
    (columns_ok T.args T.ws T.values T.lay T.positive T.edi T.inverse T.small) ET
  have CU := context_keep_columns CS valid.lay.header R.lay.scr valid.outIndex KS (by decide) OS
  have CV := context_keep_columns CT valid.lay.header T.lay.scr valid.outIndex KT (by decide) OT
  have du : PtrAt u g.W .edi g.S := by rw [PtrAt, KS.1 .edi (by decide)]; exact R.edi
  have dv : PtrAt v g.W .edi g.S := by rw [PtrAt, KT.1 .edi (by decide)]; exact T.edi
  have sp' : u.gpr .esp = v.gpr .esp := by rw [KS.1 .esp (by decide), KT.1 .esp (by decide), sp]
  have agree := timing_args_agree CU.args CV.args CU.wf CV.wf sp'
  have pair : Compact.Pair g [.ebp, .edi] u v := by
    refine ⟨CU, CV, Compact.timing_add_regs agree ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (BS.trans BT.symm)
    · exact BitVec.eq_of_toNat_eq (du.trans dv.symm)
  exact ⟨trace, pair, du, dv, BS, BT⟩

end VG.Proof.Mont.X86.PreparedSquare
