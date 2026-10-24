module

import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Record
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State

/-! Each record's trace uses only public widths, pointers, and the fixed comparison loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem record_ct {base src sp table : BitVec 32} {k offset : Nat} {dom : List Byte}
    (g : Group) (lenFit : g.len < 2 ^ 32)  :
    RelCT isa (fun s t =>
      Context base src sp table k dom s ∧
      Context base src sp table k dom t)
      (record g offset) (fun _ _ => True) := by
  let P := fun s : State => Context base src sp table k dom s
  let H := fun s : State => P s ∧ s.zf = some (decide (g.len = k))
  let A := fun s : State => Context base src sp table k dom s ∧
    s.gpr .esi = src ∧ s.gpr .edi = table + BitVec.ofNat 32 (offset + 8) ∧
    s.gpr .ecx = BitVec.ofNat 32 dom.length
  have headerCT : RelCT isa (fun s t => P s ∧ P t) (.block (header g)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp]) _ (hc := .block []) (by rfl)
    intro s t h
    apply agree_regs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.stack.trans h.2.stack.symm
  have headerWP (s : State) (h : P s) : WP isa (.block (header g)) s H := by
    refine WP.mono_syms (header_ok h g lenFit) ?_
    rintro t ⟨zero, mem, rest⟩ _sym
    exact ⟨h.after mem rest, zero⟩
  have argsCT : RelCT isa (fun s t => P s ∧ P t) (.block (compareArgs offset)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .ebx]) _ (hc := .block []) (by rfl)
    intro s t h
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.stack.trans h.2.stack.symm
    · exact h.1.baseReg.trans h.2.baseReg.symm
  have argsWP (s : State) (h : P s) : WP isa (.block (compareArgs offset)) s A := by
    refine WP.mono (args_ok h) ?_
    rintro t ⟨src, ptr, length, mem, rest⟩
    exact ⟨h.after mem rest, src, ptr, length⟩
  have compareCT : RelCT isa (fun s t => A s ∧ A t)
      VG.Impl.RsaPkcs1Sig.X86.compare (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esi, .edi, .ecx]) _ (by taint_decide)
    intro s t h
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  have compareStage := ((argsCT.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq compareCT
  have choice : RelCT isa (fun s t => H s ∧ H t)
      (.ite .e (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86.compare) (.block [.mov .ebp (.imm 1)]))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
    · exact compareStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
    · apply RelCT.taint (A := taint) (τr []) _ (hc := .block []) (by rfl)
      intro _ _ _
      exact agree_regs (by simp)
  have testCT : RelCT isa (fun _ _ => True) (.block [.alu .test .ebp (.reg .ebp)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) _ (by taint_decide)
    intro _ _ _
    exact agree_regs (by simp)
  unfold record
  exact ((headerCT.wp (fun s t h => ⟨headerWP s h.1, headerWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq (choice.seq testCT)

end VG.Proof.Ffdh.X86.VettedValidation
