module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoadState
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Static-table loads depend only on the public table index -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem StateAt.cursorLoad {g : Geometry} {c i q : Nat} {s : State} (S : StateAt g c i q s) :
    WP isa (.block [.mov .edx (.mem (slot 8))]) s fun t =>
      t.gpr .edx = g.cursor i ∧ t.gpr .esp = g.sp := by
  refine wp_movS (S.context.stack.read 8 (by decide)) fun t T _ => WP.block_nil ?_
  exact ⟨T.gpr.trans S.cursor, (T.other .esp (by decide)).trans S.context.stack.sp⟩

theorem cursorLoad_trace {g : Geometry} {c d i q : Nat} :
    RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (.block [.mov .edx (.mem (slot 8))]) (VG.X86.Taint.Agree (τr [.esp, .edx])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have before : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact S.context.stack.sp.trans T.context.stack.sp.symm)
  have trace := ((checkedBlockInvariant rfl rfl : RelCT isa
    (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edx (.mem (slot 8))])
    (VG.X86.Taint.Agree (τr [.esp]))) _ _ _ _ _ _ before E G).1
  obtain ⟨Du, Pu⟩ := wp_result S.cursorLoad E
  obtain ⟨Dz, Pz⟩ := wp_result T.cursorLoad G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact Pu.trans Pz.symm
  · exact Du.trans Dz.symm

theorem loadPrime_trace {g : Geometry} (v : g.Valid) {c d i q : Nat} (index : i < 1024) :
    RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (.block (loadPrime stackSlots)) (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) := by
  have raw : RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (.block (loadPrime stackSlots)) (VG.X86.Taint.Agree (τr [.esp])) := by
    change RelCT isa _ (.block ([.mov .edx (.mem (slot 8))] ++ [.mov .ebx (.mem ⟨.edx, 0⟩),
      .mov .esi (.mem ⟨.edx, 4⟩), .mov .edi (.mem (slot 0)), .mov .ebp (.imm 0)])) _
    exact RelCT.block_append (RelCT.seq cursorLoad_trace
      (checkedProgramChange (hint := .block []) (τ' := τr [.esp, .edx, .ebp]) rfl rfl))
  intro s t tr ur u z ⟨S, T⟩ E G
  have trace := (raw _ _ _ _ _ _ ⟨S, T⟩ E G).1
  obtain ⟨U, Pu⟩ := wp_result (S.load v index) E
  obtain ⟨Z, Pz⟩ := wp_result (T.load v index) G
  exact ⟨trace, U.readControl Pu, Z.readControl Pz⟩

end VG.Proof.RsaKeyGen.X86.Sieve
