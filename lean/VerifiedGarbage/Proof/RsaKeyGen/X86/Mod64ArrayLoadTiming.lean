module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Republish the public descending pointer before loading secret candidate data -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayState.agree {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} {s t : State}
    (S : ArrayState g candidate exponent i s) (T : ArrayState g other otherExponent i t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.context.stack.sp.trans T.context.stack.sp.symm
  · exact S.context.workspace.trans T.context.workspace.symm

theorem pointerLoad_ok {g : ArrayGeometry} {candidate exponent i : Nat} {s : State}
    (S : ArrayState g candidate exponent i s) :
    WP isa (.block [.mov .eax (.mem (stack 0))]) s fun t =>
      t.gpr .eax = g.pointer i ∧ t.gpr .esp = g.sp ∧ t.gpr .edi = g.workspace := by
  refine wp_movS (S.context.stack.read 0 (by decide)) fun t T _ => WP.block_nil ?_
  exact ⟨T.gpr.trans S.pointer, (T.other .esp (by decide)).trans S.context.stack.sp,
    (T.other .edi (by decide)).trans S.context.workspace⟩

theorem pointerLoad_trace {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent i s ∧ ArrayState g other otherExponent i t)
      (.block [.mov .eax (.mem (stack 0))]) (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have trace := ((checkedBlockInvariant (τ := τr [.esp, .edi]) (code := [.mov .eax (.mem (stack 0))]) rfl rfl)
    _ _ _ _ _ _ (S.agree T) E G).1
  obtain ⟨Au, Su, Wu⟩ := wp_result (pointerLoad_ok S) E
  obtain ⟨Az, Sz, Wz⟩ := wp_result (pointerLoad_ok T) G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact Su.trans Sz.symm
  · exact Wu.trans Wz.symm
  · exact Au.trans Az.symm

theorem loadWord_trace {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent i s ∧ ArrayState g other otherExponent i t)
      (.block loadWord) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  change RelCT isa _ (.block ([.mov .eax (.mem (stack 0))] ++ [.mov .esi (.mem ⟨.eax, 0⟩)])) _
  exact RelCT.block_append (RelCT.seq pointerLoad_trace
    (checkedProgramChange (τ' := τr [.esp, .edi, .eax]) (hint := .block []) rfl rfl))

end VG.Proof.RsaKeyGen.X86.Mod64
